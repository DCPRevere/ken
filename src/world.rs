//! Compiling declarations into resolved worlds.

use crate::ast::*;
use crate::value::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    Bool,
    Int,
    Enum(String, Vec<Rc<str>>),
    Range(i64, i64),
    Record(String, Vec<(String, Ty)>),
    Group(String),
    Content,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Travel {
    Overwrite,
    Branching,
    Fixed,
}

#[derive(Clone, Debug)]
pub struct AgentInfo {
    pub name: String,
    pub mode: Mode,
    pub sees_all_of: Option<usize>,
    /// For a segment such as Ada#2: the base person's first segment.
    pub person: Option<u32>,
}

#[derive(Clone, Debug)]
pub struct FactInfo {
    pub name: String,
    pub params: Vec<Ty>,
    pub ty: Ty,
    pub default: Option<E>,
    pub domain: Option<Vec<Value>>,
}

#[derive(Clone, Debug)]
pub struct SlotInfo {
    pub fact: String,
    pub args: Vec<Value>,
    pub domain: Vec<Value>,
}

#[derive(Clone, Debug)]
pub struct ActionInfo {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub needs: Vec<E>,
    pub effects: Vec<Assign>,
    pub seen_by: Option<Vec<SeenItem>>,
}

#[derive(Clone, Debug)]
pub struct RuleInfo {
    pub name: String,
    pub private: bool,
    pub trigger: Trigger,
    pub for_every: Option<(String, String)>,
    pub when: Option<E>,
    pub then: RuleThen,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Step {
    pub label: String,
    pub actions: Vec<Call>,
    pub env: Env,
    pub because: Option<E>,
    pub seen_by: Option<Vec<SeenItem>>,
    pub conclusions: Vec<Conclusion>,
    pub assigns: Vec<Assign>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct SegmentInfo {
    pub agent: u32,
    pub origin_world: usize,
    pub origin_agent: String,
    pub at: TimeRef,
    pub span: Span,
}

#[derive(Debug)]
pub struct World {
    pub id: usize,
    pub name: String,
    pub implicit: bool,
    pub about: Vec<usize>,
    pub revises: Option<(usize, String)>,
    pub agents: Vec<AgentInfo>,
    pub agent_names: HashMap<String, u32>,
    pub groups: HashMap<String, Vec<u32>>,
    pub types: HashMap<String, Ty>,
    pub consts: HashMap<String, String>,
    pub facts: HashMap<String, FactInfo>,
    pub slots: Vec<SlotInfo>,
    pub slot_of: HashMap<(String, Vec<Value>), usize>,
    pub actions: HashMap<String, ActionInfo>,
    pub rules: Vec<RuleInfo>,
    pub steps: Vec<Step>,
    pub label_index: HashMap<String, usize>,
    pub expects: Vec<Expect>,
    pub segments: Vec<SegmentInfo>,
    pub changeable: HashSet<String>,
    pub relevant: HashSet<usize>,
    pub honest_relevant: bool,
}

pub struct Program {
    pub file: String,
    pub src: String,
    pub worlds: Vec<World>,
    pub top_expects: Vec<Expect>,
    pub travel: Travel,
    pub allow_bootstrap: bool,
    pub params: HashMap<String, i64>,
}

impl Program {
    pub fn text(&self, s: Span) -> &str {
        self.src.get(s.start..s.end).unwrap_or("?").trim()
    }
    pub fn world_by_name(&self, n: &str) -> Option<usize> {
        self.worlds.iter().position(|w| w.name == n)
    }
    pub fn agent_name(&self, w: u16, a: u32) -> String {
        self.worlds[w as usize].agents[a as usize].name.clone()
    }
    pub fn show(&self, v: &Value) -> String {
        match v {
            Value::Bool(b) => b.to_string(),
            Value::Int(n) => n.to_string(),
            Value::Sym(s) => s.to_string(),
            Value::Agent(w, a) => self.agent_name(*w, *a),
            Value::Tuple(xs) => format!("({})", xs.iter().map(|x| self.show(x)).collect::<Vec<_>>().join(", ")),
            Value::Unknown => "?".into(),
            Value::Formula(f) => self.text(f.expr.span).to_string(),
            Value::Event(e) => match e.seen_by {
                Some((w, a)) => format!("{} as seen by {}", e.label, self.agent_name(w, a)),
                None => e.label.clone(),
            },
        }
    }
    pub fn show_action(&self, a: &ActionInst) -> String {
        format!("{}({})", a.name, a.args.iter().map(|x| self.show(x)).collect::<Vec<_>>().join(", "))
    }
    pub fn show_actions(&self, xs: &[ActionInst]) -> String {
        xs.iter().map(|a| self.show_action(a)).collect::<Vec<_>>().join(" then ")
    }
}

pub type CResult<T> = Result<T, (usize, String)>;

pub const PRELUDE: &str = include_str!("prelude.ken");

/// Evaluate a constant integer expression (ranges, parameters, loop variables).
pub fn const_int(e: &E, params: &HashMap<String, i64>, env: &Env) -> CResult<i64> {
    match &e.kind {
        ExprKind::Int(n) => Ok(*n),
        ExprKind::Name(n) => {
            if let Some(Value::Int(v)) = env_get(env, n) {
                return Ok(*v);
            }
            params.get(n).copied().ok_or((e.span.line, format!("'{}' is not a known number", n)))
        }
        ExprKind::Neg(a) => Ok(-const_int(a, params, env)?),
        ExprKind::Bin(op, a, b) => {
            let (x, y) = (const_int(a, params, env)?, const_int(b, params, env)?);
            match op {
                BinOp::Add => Ok(x + y),
                BinOp::Sub => Ok(x - y),
                BinOp::Mul => Ok(x * y),
                _ => Err((e.span.line, "expected a number".into())),
            }
        }
        _ => Err((e.span.line, "expected a number".into())),
    }
}

pub fn compile(file: &str, src: &str, decls: Vec<Decl>, prelude: Vec<Decl>, given: &HashMap<String, i64>) -> CResult<Program> {
    let mut travel = Travel::Overwrite;
    let mut allow_bootstrap = false;
    let mut params: HashMap<String, i64> = HashMap::new();
    let mut top: Vec<Decl> = Vec::new();
    let mut world_decls: Vec<(String, Vec<String>, Option<(String, TimeRef)>, Vec<Decl>, Span)> = Vec::new();
    let mut top_expects = Vec::new();

    for d in decls {
        match d {
            Decl::TimeTravel(m, _) => {
                travel = match m.as_str() {
                    "branching" => Travel::Branching,
                    "fixed" => Travel::Fixed,
                    _ => Travel::Overwrite,
                }
            }
            Decl::AllowBootstrap => allow_bootstrap = true,
            Decl::Given(items) => {
                for (n, v) in items {
                    if let Some(x) = given.get(&n) {
                        params.insert(n, *x);
                    } else if let Some(v) = v {
                        let x = const_int(&v, &params, &vec![])?;
                        params.insert(n, x);
                    } else {
                        return Err((0, format!("parameter '{}' needs a value: pass --given {}=…", n, n)));
                    }
                }
            }
            Decl::World { name, about, revises, decls, span } => world_decls.push((name, about, revises, decls, span)),
            Decl::Expect(e) => top_expects.push(e),
            other => top.push(other),
        }
    }
    for (k, v) in given {
        params.entry(k.clone()).or_insert(*v);
    }

    let has_worlds = !world_decls.is_empty();
    if has_worlds && top.iter().any(|d| !matches!(d, Decl::Expect(_))) {
        return Err((0, "when a file declares worlds, put agents, facts and timelines inside them".into()));
    }
    if !has_worlds {
        world_decls.push(("main".into(), vec![], None, top, Span::default()));
    }

    let names: Vec<String> = world_decls.iter().map(|w| w.0.clone()).collect();
    let mut worlds: Vec<World> = Vec::new();
    // AST-level copy for `revises`
    let mut raw: Vec<Vec<Decl>> = Vec::new();
    for (i, (name, about, revises, decls, _span)) in world_decls.iter().enumerate() {
        let mut ds: Vec<Decl> = prelude.clone();
        let mut revises_idx = None;
        if let Some((base, from)) = revises {
            let bi = names.iter().position(|n| n == base).ok_or((0, format!("world '{}' revises unknown world '{}'", name, base)))?;
            if bi >= i {
                return Err((0, format!("world '{}' must come after '{}', which it revises", name, base)));
            }
            let from_label = match from {
                TimeRef::Start => "start".to_string(),
                TimeRef::Event { label, .. } => label.clone(),
                _ => return Err((0, "revises … from needs an event name".into())),
            };
            for d in &raw[bi] {
                match d {
                    Decl::Timeline(evs) => {
                        let mut kept = Vec::new();
                        let mut found = false;
                        for e in evs {
                            kept.push(e.clone());
                            if e.label == from_label {
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            return Err((0, format!("world '{}' has no event '{}'", base, from_label)));
                        }
                        ds.push(Decl::Timeline(kept));
                    }
                    Decl::Expect(_) => {}
                    other => {
                        if !is_prelude_decl(other) {
                            ds.push(other.clone())
                        }
                    }
                }
            }
            revises_idx = Some((bi, from_label));
        }
        let own: Vec<Decl> = decls.clone();
        let mut own_raw = Vec::new();
        for d in &ds {
            if !is_prelude_decl(d) {
                own_raw.push(d.clone());
            }
        }
        own_raw.extend(own.iter().cloned());
        raw.push(own_raw);
        ds.extend(own);
        let about_idx = about
            .iter()
            .map(|a| names.iter().position(|n| n == a).ok_or((0, format!("world '{}' is about unknown world '{}'", name, a))))
            .collect::<CResult<Vec<_>>>()?;
        let w = compile_world(i, name, !has_worlds, about_idx, revises_idx, ds, &params, &names)?;
        worlds.push(w);
    }
    // segment origin worlds are resolved; mark relevance from all author expressions
    let mut prog = Program { file: file.into(), src: src.into(), worlds, top_expects, travel, allow_bootstrap, params };
    compute_relevance(&mut prog, &raw);
    Ok(prog)
}

fn is_prelude_decl(d: &Decl) -> bool {
    match d {
        Decl::Fact { name, .. } => name == "honest",
        Decl::Action { name, .. } => name == "tell" || name == "announce",
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_world(
    id: usize,
    name: &str,
    implicit: bool,
    about: Vec<usize>,
    revises: Option<(usize, String)>,
    decls: Vec<Decl>,
    params: &HashMap<String, i64>,
    world_names: &[String],
) -> CResult<World> {
    let mut w = World {
        id,
        name: name.into(),
        implicit,
        about,
        revises,
        agents: vec![],
        agent_names: HashMap::new(),
        groups: HashMap::new(),
        types: HashMap::new(),
        consts: HashMap::new(),
        facts: HashMap::new(),
        slots: vec![],
        slot_of: HashMap::new(),
        actions: HashMap::new(),
        rules: vec![],
        steps: vec![],
        label_index: HashMap::new(),
        expects: vec![],
        segments: vec![],
        changeable: HashSet::new(),
        relevant: HashSet::new(),
        honest_relevant: false,
    };
    w.groups.insert("Agent".into(), vec![]);
    let mut taken: HashMap<String, &'static str> = HashMap::new();
    let mut claim = |n: &str, what: &'static str, line: usize| -> CResult<()> {
        if let Some(prev) = taken.get(n) {
            return Err((line, format!("'{}' is already used as {}; names must be unique", n, prev)));
        }
        taken.insert(n.to_string(), what);
        Ok(())
    };
    for p in params.keys() {
        claim(p, "a parameter", 0)?;
    }

    // pass 1: agents and types
    for d in &decls {
        match d {
            Decl::Agent { names, mode, sees_all_of, span } => {
                let sees = match sees_all_of {
                    Some(n) => Some(world_names.iter().position(|x| x == n).ok_or((span.line, format!("unknown world '{}'", n)))?),
                    None => None,
                };
                for an in names {
                    match &an.range {
                        None => {
                            claim(&an.base, "an agent", span.line)?;
                            let ix = w.agents.len() as u32;
                            w.agents.push(AgentInfo { name: an.base.clone(), mode: mode.unwrap_or(Mode::Person), sees_all_of: sees, person: None });
                            w.agent_names.insert(an.base.clone(), ix);
                            w.groups.get_mut("Agent").unwrap().push(ix);
                        }
                        Some((lo, hi)) => {
                            claim(&an.base, "an agent group", span.line)?;
                            let lo = const_int(lo, params, &vec![])?;
                            let hi = const_int(hi, params, &vec![])?;
                            let mut members = vec![];
                            for k in lo..=hi {
                                let nm = format!("{}[{}]", an.base, k);
                                let ix = w.agents.len() as u32;
                                w.agents.push(AgentInfo { name: nm.clone(), mode: mode.unwrap_or(Mode::Person), sees_all_of: sees, person: None });
                                w.agent_names.insert(nm, ix);
                                w.groups.get_mut("Agent").unwrap().push(ix);
                                members.push(ix);
                            }
                            w.groups.insert(an.base.clone(), members);
                            w.types.insert(an.base.clone(), Ty::Group(an.base.clone()));
                        }
                    }
                }
            }
            Decl::Type { name: tn, def, span } => {
                claim(tn, "a type", span.line)?;
                let ty = match def {
                    TypeDef::Enum(vs) => {
                        for v in vs {
                            claim(v, "a constant", span.line)?;
                            w.consts.insert(v.clone(), tn.clone());
                        }
                        Ty::Enum(tn.clone(), vs.iter().map(|s| Rc::from(s.as_str())).collect())
                    }
                    TypeDef::Range(lo, hi) => Ty::Range(const_int(lo, params, &vec![])?, const_int(hi, params, &vec![])?),
                    TypeDef::Record(fields) => {
                        let mut fs = vec![];
                        for (f, t) in fields {
                            fs.push((f.clone(), resolve_ty(&w, t, params, span.line)?));
                        }
                        Ty::Record(tn.clone(), fs)
                    }
                };
                w.types.insert(tn.clone(), ty);
            }
            _ => {}
        }
    }
    // segments
    for d in &decls {
        if let Decl::Segment { name: sn, origin_world, origin, at, span } = d {
            let ow = match origin_world {
                Some(n) => world_names.iter().position(|x| x == n).ok_or((span.line, format!("unknown world '{}'", n)))?,
                None => id,
            };
            let base = sn.split('#').next().unwrap().to_string();
            let base_ix = *w.agent_names.get(&base).ok_or((span.line, format!("segment '{}' needs an agent '{}' in this world", sn, base)))?;
            claim(sn, "an agent", span.line)?;
            let ix = w.agents.len() as u32;
            let mode = w.agents[base_ix as usize].mode;
            w.agents.push(AgentInfo { name: sn.clone(), mode, sees_all_of: None, person: Some(base_ix) });
            w.agent_names.insert(sn.clone(), ix);
            w.agent_names.insert(format!("{}#1", base), base_ix);
            w.groups.get_mut("Agent").unwrap().push(ix);
            w.segments.push(SegmentInfo { agent: ix, origin_world: ow, origin_agent: origin.clone(), at: at.clone(), span: *span });
        }
    }
    // pass 2: facts, actions, rules
    for d in &decls {
        match d {
            Decl::Fact { name: fname, params: ps, ty, default, domain, span } => {
                if w.facts.contains_key(fname) {
                    continue; // re-declared via revises copy
                }
                claim(fname, "a fact", span.line)?;
                let pts = ps.iter().map(|t| resolve_ty(&w, t, params, span.line)).collect::<CResult<Vec<_>>>()?;
                let fty = resolve_ty(&w, ty, params, span.line)?;
                let dom = match domain {
                    Some(vs) => Some(vs.iter().map(|e| const_value(&w, e, params, &fty)).collect::<CResult<Vec<_>>>()?),
                    None => None,
                };
                w.facts.insert(fname.clone(), FactInfo { name: fname.clone(), params: pts, ty: fty, default: default.clone(), domain: dom });
            }
            Decl::Action { name: an, params: ps, needs, effects, seen_by, span } => {
                if w.actions.contains_key(an) {
                    continue;
                }
                claim(an, "an action", span.line)?;
                let pts = ps
                    .iter()
                    .map(|(n, t)| Ok((n.clone(), match t { Some(t) => resolve_ty(&w, t, params, span.line)?, None => Ty::Content })))
                    .collect::<CResult<Vec<_>>>()?;
                for e in effects {
                    if let Some(f) = assign_fact(e) {
                        w.changeable.insert(f);
                    }
                }
                w.actions.insert(an.clone(), ActionInfo { name: an.clone(), params: pts, needs: needs.clone(), effects: effects.clone(), seen_by: seen_by.clone() });
            }
            Decl::Rule { name: rn, private, trigger, for_every, when, then, span } => {
                w.rules.push(RuleInfo { name: rn.clone(), private: *private, trigger: trigger.clone(), for_every: for_every.clone(), when: when.clone(), then: then.clone(), span: *span });
            }
            _ => {}
        }
    }
    // slots
    let fact_names: Vec<String> = {
        let mut v: Vec<String> = w.facts.keys().cloned().collect();
        v.sort();
        v
    };
    for fname in fact_names {
        let f = w.facts[&fname].clone();
        let mut combos: Vec<Vec<Value>> = vec![vec![]];
        for pt in &f.params {
            let dom = domain_of(&w, pt).ok_or((0, format!("fact '{}' has a parameter with no finite domain", fname)))?;
            let mut next = vec![];
            for c in &combos {
                for v in &dom {
                    let mut c2 = c.clone();
                    c2.push(v.clone());
                    next.push(c2);
                }
            }
            combos = next;
        }
        let dom = match &f.domain {
            Some(d) => d.clone(),
            None => domain_of(&w, &f.ty).unwrap_or_default(),
        };
        for args in combos {
            let ix = w.slots.len();
            w.slot_of.insert((fname.clone(), args.clone()), ix);
            w.slots.push(SlotInfo { fact: fname.clone(), args, domain: dom.clone() });
        }
    }
    // timeline and expects
    for d in decls {
        match d {
            Decl::Timeline(evs) => {
                for ev in evs {
                    let mut seen_by = None;
                    let mut conclusions = vec![];
                    let mut assigns = vec![];
                    for c in &ev.clauses {
                        match c {
                            EventClause::SeenBy(s, _) => {
                                let mut all = seen_by.take().unwrap_or_else(Vec::new);
                                all.extend(s.iter().cloned());
                                seen_by = Some(all);
                            }
                            EventClause::Concludes(c) => conclusions.push(c.clone()),
                            EventClause::Assign(a) => assigns.push(a.clone()),
                        }
                    }
                    let mk = |label: String, env: Env| Step {
                        label,
                        actions: ev.actions.clone(),
                        env,
                        because: ev.because.clone(),
                        seen_by: seen_by.clone(),
                        conclusions: conclusions.clone(),
                        assigns: assigns.clone(),
                        span: ev.span,
                    };
                    let mut new_steps = vec![];
                    match &ev.repeat {
                        None => new_steps.push(mk(ev.label.clone(), vec![])),
                        Some((v, lo, hi)) => {
                            let lo = const_int(lo, params, &vec![])?;
                            let hi = const_int(hi, params, &vec![])?;
                            for k in lo..=hi {
                                let env: Env = vec![(Rc::from(v.as_str()), Value::Int(k))];
                                let args = ev.label_args.iter().map(|a| const_int(a, params, &env).map(|x| x.to_string())).collect::<CResult<Vec<_>>>()?;
                                new_steps.push(mk(format!("{}({})", ev.label, args.join(", ")), env));
                            }
                        }
                    }
                    for s in new_steps {
                        if s.label == "start" && !w.steps.is_empty() {
                            return Err((s.span.line, "'start' must be the first event".into()));
                        }
                        if w.steps.is_empty() && s.label != "start" {
                            // implicit empty start
                            w.label_index.insert("start".into(), 0);
                            w.steps.push(Step { label: "start".into(), actions: vec![], env: vec![], because: None, seen_by: None, conclusions: vec![], assigns: vec![], span: s.span });
                        }
                        if w.label_index.contains_key(&s.label) {
                            return Err((s.span.line, format!("event '{}' is defined twice", s.label)));
                        }
                        w.label_index.insert(s.label.clone(), w.steps.len());
                        w.steps.push(s);
                    }
                }
            }
            Decl::Expect(e) => w.expects.push(e),
            _ => {}
        }
    }
    if w.steps.is_empty() {
        w.label_index.insert("start".into(), 0);
        w.steps.push(Step { label: "start".into(), actions: vec![], env: vec![], because: None, seen_by: None, conclusions: vec![], assigns: vec![], span: Span::default() });
    }
    Ok(w)
}

fn assign_fact(a: &Assign) -> Option<String> {
    match &a.target.kind {
        ExprKind::Name(n) => Some(n.clone()),
        ExprKind::Call(n, _) => Some(n.clone()),
        _ => None,
    }
}

pub fn resolve_ty(w: &World, t: &TypeRef, params: &HashMap<String, i64>, line: usize) -> CResult<Ty> {
    match t {
        TypeRef::Range(lo, hi) => Ok(Ty::Range(const_int(lo, params, &vec![])?, const_int(hi, params, &vec![])?)),
        TypeRef::Named(n) => match n.as_str() {
            "bool" | "Bool" => Ok(Ty::Bool),
            "Int" | "int" => Ok(Ty::Int),
            "Agent" => Ok(Ty::Group("Agent".into())),
            _ => w.types.get(n).cloned().ok_or((line, format!("unknown type '{}'", n))),
        },
    }
}

pub fn domain_of(w: &World, t: &Ty) -> Option<Vec<Value>> {
    match t {
        Ty::Bool => Some(vec![Value::Bool(false), Value::Bool(true)]),
        Ty::Int | Ty::Content => None,
        Ty::Enum(_, vs) => Some(vs.iter().map(|s| Value::Sym(s.clone())).collect()),
        Ty::Range(lo, hi) => Some((*lo..=*hi).map(Value::Int).collect()),
        Ty::Group(g) => Some(w.groups.get(g)?.iter().map(|a| Value::Agent(w.id as u16, *a)).collect()),
        Ty::Record(_, fs) => {
            let mut combos: Vec<Vec<Value>> = vec![vec![]];
            for (_, ft) in fs {
                let d = domain_of(w, ft)?;
                let mut next = vec![];
                for c in &combos {
                    for v in &d {
                        let mut c2 = c.clone();
                        c2.push(v.clone());
                        next.push(c2);
                    }
                }
                combos = next;
                if combos.len() > 100_000 {
                    return None;
                }
            }
            Some(combos.into_iter().map(|c| Value::Tuple(c.into())).collect())
        }
    }
}

/// A literal value at compile time (fact domains).
pub fn const_value(w: &World, e: &E, params: &HashMap<String, i64>, _ty: &Ty) -> CResult<Value> {
    match &e.kind {
        ExprKind::Int(_) | ExprKind::Neg(_) | ExprKind::Bin(..) => Ok(Value::Int(const_int(e, params, &vec![])?)),
        ExprKind::Bool(b) => Ok(Value::Bool(*b)),
        ExprKind::Name(n) => {
            if w.consts.contains_key(n) {
                Ok(Value::Sym(Rc::from(n.as_str())))
            } else if let Some(a) = w.agent_names.get(n) {
                Ok(Value::Agent(w.id as u16, *a))
            } else if let Some(v) = params.get(n) {
                Ok(Value::Int(*v))
            } else {
                Err((e.span.line, format!("'{}' is not a constant", n)))
            }
        }
        ExprKind::Tuple(xs) => Ok(Value::Tuple(xs.iter().map(|x| const_value(w, x, params, &Ty::Int)).collect::<CResult<Vec<_>>>()?.into())),
        _ => Err((e.span.line, "expected a constant".into())),
    }
}

// ------------------------------------------------------------------ relevance

/// A slot is relevant if author code ever reads it. Only relevant slots vary
/// between possible worlds, which keeps models small.
fn compute_relevance(prog: &mut Program, raw: &[Vec<Decl>]) {
    let mut reads: Vec<(String, Option<Vec<E>>)> = Vec::new();
    let mut honest_written = false;
    let mut all_exprs: Vec<E> = Vec::new();
    for e in &prog.top_expects {
        all_exprs.extend(e.formulas.iter().cloned());
    }
    for ds in raw {
        for d in ds {
            collect_decl_exprs(d, &mut all_exprs, &mut honest_written);
        }
    }
    for e in &all_exprs {
        collect_reads(e, &mut reads);
    }
    for w in prog.worlds.iter_mut() {
        let mut rel = HashSet::new();
        for (f, args) in &reads {
            if !w.facts.contains_key(f) {
                continue;
            }
            if f == "honest" {
                w.honest_relevant = true;
            }
            let ground: Option<Vec<Value>> = args.as_ref().and_then(|a| {
                a.iter()
                    .map(|x| match &x.kind {
                        ExprKind::Name(n) => w
                            .agent_names
                            .get(n)
                            .map(|i| Value::Agent(w.id as u16, *i))
                            .or_else(|| w.consts.get(n).map(|_| Value::Sym(Rc::from(n.as_str())))),
                        ExprKind::Int(k) => Some(Value::Int(*k)),
                        _ => None,
                    })
                    .collect()
            });
            for (ix, s) in w.slots.iter().enumerate() {
                if &s.fact == f {
                    match &ground {
                        Some(g) if g.len() == s.args.len() => {
                            if *g == s.args {
                                rel.insert(ix);
                            }
                        }
                        _ => {
                            rel.insert(ix);
                        }
                    }
                }
            }
        }
        if honest_written {
            w.honest_relevant = true;
        }
        if !w.honest_relevant {
            rel.retain(|ix| w.slots[*ix].fact != "honest");
        } else {
            for (ix, s) in w.slots.iter().enumerate() {
                if s.fact == "honest" {
                    rel.insert(ix);
                }
            }
        }
        w.relevant = rel;
    }
}

fn collect_decl_exprs(d: &Decl, out: &mut Vec<E>, honest_written: &mut bool) {
    match d {
        Decl::Action { name, needs, effects, seen_by, .. } => {
            if name == "tell" || name == "announce" {
                return;
            }
            out.extend(needs.iter().cloned());
            for e in effects {
                out.push(e.value.clone());
            }
            if let Some(s) = seen_by {
                seen_exprs(s, out);
            }
        }
        Decl::Rule { when, then, trigger, .. } => {
            if let Some(w) = when {
                out.push(w.clone());
            }
            if let RuleThen::Concludes(_, f) = then {
                out.push(f.clone());
            }
            let _ = trigger;
        }
        Decl::Timeline(evs) => {
            for ev in evs {
                if let Some(b) = &ev.because {
                    out.push(b.clone());
                }
                for a in &ev.actions {
                    out.extend(a.args.iter().cloned());
                }
                for c in &ev.clauses {
                    match c {
                        EventClause::SeenBy(s, _) => seen_exprs(s, out),
                        EventClause::Concludes(c) => {
                            out.push(c.formula.clone());
                            if let Some(b) = &c.because {
                                out.push(b.clone());
                            }
                        }
                        EventClause::Assign(a) => {
                            if assign_fact(a).as_deref() == Some("honest") {
                                *honest_written = true;
                            }
                        }
                    }
                }
            }
        }
        Decl::Expect(e) => out.extend(e.formulas.iter().cloned()),
        _ => {}
    }
}

fn seen_exprs(s: &[SeenItem], out: &mut Vec<E>) {
    for it in s {
        if let Who::Every { cond: Some(c), .. } = &it.who {
            out.push(c.clone());
        }
    }
}

fn collect_reads(e: &E, out: &mut Vec<(String, Option<Vec<E>>)>) {
    match &e.kind {
        ExprKind::Name(n) => out.push((n.clone(), Some(vec![]))),
        ExprKind::Qualified(_, n) => out.push((n.clone(), Some(vec![]))),
        ExprKind::Call(n, args) => {
            out.push((n.clone(), Some(args.clone())));
            for a in args {
                collect_reads(a, out);
            }
        }
        ExprKind::Index(_, i) => collect_reads(i, out),
        ExprKind::Field(b, _) => collect_reads(b, out),
        ExprKind::Tuple(xs) => xs.iter().for_each(|x| collect_reads(x, out)),
        ExprKind::Not(a) | ExprKind::Neg(a) => collect_reads(a, out),
        ExprKind::Bin(_, a, b) => {
            collect_reads(a, out);
            collect_reads(b, out);
        }
        ExprKind::Quant { body, .. } | ExprKind::Common { body, .. } => collect_reads(body, out),
        ExprKind::Epistemic { agent, body, .. } | ExprKind::Deducible { agent, body } | ExprKind::Possible { agent, body } => {
            collect_reads(agent, out);
            collect_reads(body, out);
        }
        ExprKind::Saw { .. } => {}
        ExprKind::At(a, _) => collect_reads(a, out),
        ExprKind::SeenAs { .. } => {}
        ExprKind::Int(_) | ExprKind::Bool(_) => {}
    }
}
