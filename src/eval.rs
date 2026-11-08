//! Evaluating formulas in a model.

use crate::ast::*;
use crate::foreign;
use crate::kripke::Model;
use crate::state::*;
use crate::value::*;
use crate::world::*;
use std::rc::Rc;

pub type R<T> = Result<T, String>;

/// Access to other worlds and times while evaluating.
pub trait Hub {
    fn snap(&self, world: usize, step: usize) -> Option<Snap>;
    fn n_steps(&self, world: usize) -> Option<usize>;
    fn deducible_model(&self, world: usize, step: usize, agent: u32) -> R<Rc<Model>>;
}

pub struct Ev<'a> {
    pub prog: &'a Program,
    pub wid: usize,
    pub model: &'a Model,
    pub step: usize,
    pub registry: Option<&'a Registry>,
    pub foreign: Option<&'a ForeignMap>,
    pub hub: Option<&'a dyn Hub>,
    pub vals: Option<&'a [Value]>,
}

impl<'a> Ev<'a> {
    pub fn world(&self) -> &'a World {
        &self.prog.worlds[self.wid]
    }

    fn slot_val(&self, w: u32, slot: usize) -> Value {
        match self.vals {
            Some(v) => v[slot].clone(),
            None => self.model.vals[w as usize][slot].clone(),
        }
    }

    pub fn truth(&self, w: u32, env: &Env, e: &E) -> R<bool> {
        match self.eval(w, env, e)? {
            Value::Bool(b) => Ok(b),
            Value::Unknown => Ok(true),
            v => Err(format!("'{}' is {}, not true or false", self.prog.text(e.span), self.prog.show(&v))),
        }
    }

    pub fn strict_truth(&self, w: u32, env: &Env, e: &E) -> R<Option<bool>> {
        match self.eval(w, env, e)? {
            Value::Bool(b) => Ok(Some(b)),
            Value::Unknown => Ok(None),
            v => Err(format!("'{}' is {}, not true or false", self.prog.text(e.span), self.prog.show(&v))),
        }
    }

    pub fn slot_index(&self, fact: &str, args: Vec<Value>) -> R<usize> {
        let w = self.world();
        let f = w.facts.get(fact).ok_or(format!("unknown fact '{}'", fact))?;
        if f.params.len() != args.len() {
            return Err(format!("'{}' takes {} argument(s)", fact, f.params.len()));
        }
        let args: Vec<Value> = f.params.iter().zip(args).map(|(t, v)| coerce(w, t, v)).collect();
        w.slot_of.get(&(fact.to_string(), args.clone())).copied().ok_or_else(|| {
            format!("{}({}) is not a valid fact", fact, args.iter().map(|a| self.prog.show(a)).collect::<Vec<_>>().join(", "))
        })
    }

    pub fn eval(&self, w: u32, env: &Env, e: &E) -> R<Value> {
        let world = self.world();
        match &e.kind {
            ExprKind::Int(n) => Ok(Value::Int(*n)),
            ExprKind::Bool(b) => Ok(Value::Bool(*b)),
            ExprKind::Name(n) => {
                if let Some(v) = env_get(env, n) {
                    if let Value::Formula(f) = v {
                        if f.world == self.wid {
                            return self.eval(w, &f.env, &f.expr);
                        }
                    }
                    return Ok(v.clone());
                }
                if let Some(v) = self.prog.params.get(n) {
                    return Ok(Value::Int(*v));
                }
                if world.facts.contains_key(n) {
                    let s = self.slot_index(n, vec![])?;
                    return Ok(self.slot_val(w, s));
                }
                if let Some(a) = world.agent_names.get(n) {
                    return Ok(Value::Agent(self.wid as u16, *a));
                }
                if world.consts.contains_key(n) {
                    return Ok(Value::Sym(Rc::from(n.as_str())));
                }
                if world.label_index.contains_key(n) {
                    return Ok(Value::Event(Rc::new(EventRef { world: self.wid, label: n.clone(), seen_by: None })));
                }
                for &o in &world.about {
                    let ow = &self.prog.worlds[o];
                    if let Some(a) = ow.agent_names.get(n) {
                        return Ok(Value::Agent(o as u16, *a));
                    }
                    if ow.consts.contains_key(n) {
                        return Ok(Value::Sym(Rc::from(n.as_str())));
                    }
                    if ow.label_index.contains_key(n) {
                        return Ok(Value::Event(Rc::new(EventRef { world: o, label: n.clone(), seen_by: None })));
                    }
                    if ow.facts.contains_key(n) {
                        return Err(format!("'{}' is a fact of world {}; only a person's beliefs can be about another world", n, ow.name));
                    }
                }
                Err(format!("unknown name '{}'", n))
            }
            ExprKind::Qualified(wn, n) => {
                let o = self.prog.world_by_name(wn).ok_or(format!("unknown world '{}'", wn))?;
                let ow = &self.prog.worlds[o];
                if let Some(a) = ow.agent_names.get(n) {
                    return Ok(Value::Agent(o as u16, *a));
                }
                if ow.label_index.contains_key(n) {
                    return Ok(Value::Event(Rc::new(EventRef { world: o, label: n.clone(), seen_by: None })));
                }
                Err(format!("'{}.{}' is not an agent or event", wn, n))
            }
            ExprKind::Call(n, args) => {
                if !world.facts.contains_key(n) {
                    for &o in &world.about {
                        if self.prog.worlds[o].facts.contains_key(n) {
                            return Err(format!("'{}' is a fact of world {}; only a person's beliefs can be about another world", n, self.prog.worlds[o].name));
                        }
                    }
                    return Err(format!("unknown fact '{}'", n));
                }
                let mut vs = Vec::new();
                for a in args {
                    let v = self.eval(w, env, a)?;
                    if v == Value::Unknown {
                        return Ok(Value::Unknown);
                    }
                    vs.push(v);
                }
                let s = self.slot_index(n, vs)?;
                Ok(self.slot_val(w, s))
            }
            ExprKind::Index(g, i) => {
                let k = self.eval(w, env, i)?.as_int().ok_or("an index must be a number")?;
                let nm = format!("{}[{}]", g, k);
                world.agent_names.get(&nm).map(|a| Value::Agent(self.wid as u16, *a)).ok_or(format!("no agent {}", nm))
            }
            ExprKind::Field(b, f) => {
                let ty = self.static_type(b).ok_or(format!("can't tell what '{}' is, to take its field '{}'", self.prog.text(b.span), f))?;
                let v = self.eval(w, env, b)?;
                if v == Value::Unknown {
                    return Ok(Value::Unknown);
                }
                match (ty, v) {
                    (Ty::Record(_, fs), Value::Tuple(xs)) => {
                        let i = fs.iter().position(|(n, _)| n == f).ok_or(format!("no field '{}'", f))?;
                        Ok(xs[i].clone())
                    }
                    _ => Err(format!("'{}' has no fields", self.prog.text(b.span))),
                }
            }
            ExprKind::Tuple(xs) => {
                let mut vs = Vec::new();
                for x in xs {
                    vs.push(self.eval(w, env, x)?);
                }
                Ok(Value::Tuple(vs.into()))
            }
            ExprKind::Not(a) => match self.eval(w, env, a)? {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                Value::Unknown => Ok(Value::Unknown),
                v => Err(format!("can't negate {}", self.prog.show(&v))),
            },
            ExprKind::Neg(a) => match self.eval(w, env, a)? {
                Value::Int(n) => Ok(Value::Int(-n)),
                _ => Err("expected a number".into()),
            },
            ExprKind::Bin(op, a, b) => self.bin(w, env, *op, a, b),
            ExprKind::Quant { all, var, ty, body } => {
                let dom = self.type_domain(ty)?;
                let mut unknown = false;
                for v in dom {
                    let env2 = env_with(env, var, v);
                    match self.eval(w, &env2, body)? {
                        Value::Bool(b) => {
                            if b != *all {
                                return Ok(Value::Bool(!*all));
                            }
                        }
                        Value::Unknown => unknown = true,
                        x => return Err(format!("expected true or false, got {}", self.prog.show(&x))),
                    }
                }
                Ok(if unknown { Value::Unknown } else { Value::Bool(*all) })
            }
            ExprKind::Epistemic { agent, mode, body } => {
                let (aw, a) = self.eval(w, env, agent)?.as_agent().ok_or(format!("'{}' is not an agent", self.prog.text(agent.span)))?;
                if aw as usize != self.wid {
                    return Err(format!(
                        "{}'s beliefs belong to world {} and change over time; write `({}) at <event>`",
                        self.prog.agent_name(aw, a),
                        self.prog.worlds[aw as usize].name,
                        self.prog.text(e.span)
                    ));
                }
                if let Some(tw) = self.foreign_world(body)? {
                    return self.foreign_epistemic(w, a, tw, *mode, env, body);
                }
                Ok(Value::Bool(self.kripke_epistemic(w, a, *mode, env, body)?))
            }
            ExprKind::Common { group, body } => {
                let members: Vec<u32> = match group {
                    Some(g) => world.groups.get(g).cloned().ok_or(format!("unknown group '{}'", g))?,
                    None => world.groups["Agent"].clone(),
                };
                let mut seen = vec![false; self.model.n()];
                let mut stack: Vec<u32> = Vec::new();
                for &a in &members {
                    for &v in self.model.succ(a, w) {
                        if !seen[v as usize] {
                            seen[v as usize] = true;
                            stack.push(v);
                        }
                    }
                }
                while let Some(v) = stack.pop() {
                    if !self.truth(v, env, body)? {
                        return Ok(Value::Bool(false));
                    }
                    for &a in &members {
                        for &u in self.model.succ(a, v) {
                            if !seen[u as usize] {
                                seen[u as usize] = true;
                                stack.push(u);
                            }
                        }
                    }
                }
                Ok(Value::Bool(true))
            }
            ExprKind::Deducible { agent, body } | ExprKind::Possible { agent, body } => {
                let deducible = matches!(e.kind, ExprKind::Deducible { .. });
                let (aw, a) = self.eval(w, env, agent)?.as_agent().ok_or("expected an agent")?;
                if aw as usize != self.wid {
                    return Err("write `(…) at <event>` to ask about an agent of another world".into());
                }
                if let Some(tw) = self.foreign_world(body)? {
                    let st = self.foreign.and_then(|f| f.get(&(a, tw))).cloned().unwrap_or_default();
                    let r = foreign::eval_obs(self.prog, tw, &st, env, body);
                    return Ok(Value::Bool(if deducible { r == Some(true) } else { r != Some(false) }));
                }
                if w != self.model.actual {
                    return Err("'deducible by' and 'possible for' can't be nested inside other beliefs".into());
                }
                let hub = self.hub.ok_or("no history available")?;
                let m = hub.deducible_model(self.wid, self.step, a)?;
                let ev = Ev { prog: self.prog, wid: self.wid, model: &m, step: self.step, registry: self.registry, foreign: self.foreign, hub: self.hub, vals: None };
                let succ = m.succ(a, m.actual).to_vec();
                if deducible {
                    for v in succ {
                        if !ev.truth(v, env, body)? {
                            return Ok(Value::Bool(false));
                        }
                    }
                    Ok(Value::Bool(true))
                } else {
                    for v in succ {
                        if ev.truth(v, env, body)? {
                            return Ok(Value::Bool(true));
                        }
                    }
                    Ok(Value::Bool(false))
                }
            }
            ExprKind::Saw { agent, what } => {
                let (aw, a) = self.eval(w, env, agent)?.as_agent().ok_or("expected an agent")?;
                if aw as usize != self.wid {
                    return Err("'saw' must refer to an agent of this world".into());
                }
                let reg = self.registry.ok_or("no record of what was seen here")?;
                let target = self.eval(w, env, what)?;
                let views = &reg.views[a as usize];
                match target {
                    Value::Event(r) => Ok(Value::Bool(views.get(&r.label).map(|v| v.direct).unwrap_or(false))),
                    Value::Agent(_, b) => {
                        let hit = views.values().any(|v| v.direct && v.actual.iter().any(|act| act.args.iter().any(|x| *x == Value::Agent(self.wid as u16, b))));
                        Ok(Value::Bool(hit))
                    }
                    _ => Err("'saw' takes an event or an agent".into()),
                }
            }
            ExprKind::At(inner, t) => {
                let hub = self.hub.ok_or("no history available")?;
                let (tw, step) = resolve_time(self.prog, self.wid, t, hub, &self.prog.params)?;
                let snap = hub.snap(tw, step).ok_or("that time hasn't been reached yet")?;
                let ev = Ev { prog: self.prog, wid: tw, model: &snap.model, step, registry: Some(&snap.registry), foreign: Some(&snap.foreign), hub: self.hub, vals: None };
                ev.eval(snap.model.actual, env, inner)
            }
            ExprKind::SeenAs { event, by } => {
                let ev = self.eval(w, env, event)?;
                let ag = self.eval(w, env, by)?.as_agent().ok_or("expected an agent after 'seen by'")?;
                match ev {
                    Value::Event(r) => Ok(Value::Event(Rc::new(EventRef { world: r.world, label: r.label.clone(), seen_by: Some(ag) }))),
                    _ => Err("expected an event before 'as seen by'".into()),
                }
            }
        }
    }

    fn bin(&self, w: u32, env: &Env, op: BinOp, a: &E, b: &E) -> R<Value> {
        use BinOp::*;
        match op {
            And | Or | Implies => {
                let x = self.eval(w, env, a)?;
                let xb = match x {
                    Value::Bool(v) => Some(v),
                    Value::Unknown => None,
                    _ => return Err(format!("'{}' is not true or false", self.prog.text(a.span))),
                };
                match (op, xb) {
                    (And, Some(false)) => return Ok(Value::Bool(false)),
                    (Or, Some(true)) => return Ok(Value::Bool(true)),
                    (Implies, Some(false)) => return Ok(Value::Bool(true)),
                    _ => {}
                }
                let y = self.eval(w, env, b)?;
                let yb = match y {
                    Value::Bool(v) => Some(v),
                    Value::Unknown => None,
                    _ => return Err(format!("'{}' is not true or false", self.prog.text(b.span))),
                };
                Ok(match (op, xb, yb) {
                    (_, Some(_), Some(y)) => Value::Bool(y),
                    (And, _, Some(false)) => Value::Bool(false),
                    (Or | Implies, _, Some(true)) => Value::Bool(true),
                    _ => Value::Unknown,
                })
            }
            Iff => {
                let x = self.eval(w, env, a)?;
                let y = self.eval(w, env, b)?;
                match (x, y) {
                    (Value::Bool(x), Value::Bool(y)) => Ok(Value::Bool(x == y)),
                    _ => Ok(Value::Unknown),
                }
            }
            Eq | Ne => {
                let x = self.eval(w, env, a)?;
                let y = self.eval(w, env, b)?;
                if x == Value::Unknown || y == Value::Unknown {
                    return Ok(Value::Unknown);
                }
                let eq = x == y;
                Ok(Value::Bool(if op == Eq { eq } else { !eq }))
            }
            Lt | Le | Gt | Ge | Add | Sub | Mul => {
                let x = self.eval(w, env, a)?;
                let y = self.eval(w, env, b)?;
                let (x, y) = match (x, y) {
                    (Value::Int(x), Value::Int(y)) => (x, y),
                    _ => return Ok(Value::Unknown),
                };
                Ok(match op {
                    Lt => Value::Bool(x < y),
                    Le => Value::Bool(x <= y),
                    Gt => Value::Bool(x > y),
                    Ge => Value::Bool(x >= y),
                    Add => Value::Int(x + y),
                    Sub => Value::Int(x - y),
                    _ => Value::Int(x * y),
                })
            }
        }
    }

    pub fn kripke_epistemic(&self, w: u32, a: u32, mode: KMode, env: &Env, body: &E) -> R<bool> {
        let succ = self.model.succ(a, w);
        let here = self.eval(w, env, body)?;
        match mode {
            KMode::KnowsWhether => {
                for &v in succ {
                    if self.eval(v, env, body)? != here {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            KMode::Believes => {
                let mut first: Option<Value> = None;
                for &v in succ {
                    let x = self.eval(v, env, body)?;
                    match &x {
                        Value::Bool(false) => return Ok(false),
                        Value::Bool(true) => {}
                        _ => {
                            if let Some(f) = &first {
                                if *f != x {
                                    return Ok(false);
                                }
                            } else {
                                first = Some(x);
                            }
                        }
                    }
                }
                Ok(true)
            }
            KMode::Knows => {
                match &here {
                    Value::Bool(false) => return Ok(false),
                    Value::Bool(true) => {}
                    _ => {
                        for &v in succ {
                            if self.eval(v, env, body)? != here {
                                return Ok(false);
                            }
                        }
                        return Ok(true);
                    }
                }
                for &v in succ {
                    if !self.truth(v, env, body)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }

    fn foreign_epistemic(&self, _w: u32, a: u32, tw: usize, mode: KMode, env: &Env, body: &E) -> R<Value> {
        let tworld = &self.prog.worlds[tw];
        // changeable facts of another world need a time
        let mut names = Vec::new();
        fact_names(body, &mut names);
        for n in names {
            if tworld.changeable.contains(&n) {
                return Err(format!("'{}' can change in world {}; say when, e.g. `{} at <event>`", n, tworld.name, n));
            }
        }
        let st = self.foreign.and_then(|f| f.get(&(a, tw))).cloned().unwrap_or_default();
        let believes = foreign::believes(self.prog, tw, &st, env, body);
        match mode {
            KMode::Believes => Ok(Value::Bool(believes)),
            KMode::Knows | KMode::KnowsWhether => {
                let hub = self.hub.ok_or("no history available")?;
                let last = hub.n_steps(tw).ok_or("that world hasn't been checked")?.saturating_sub(1);
                let snap = hub.snap(tw, last).ok_or("that world hasn't been checked")?;
                let ev = Ev { prog: self.prog, wid: tw, model: &snap.model, step: last, registry: Some(&snap.registry), foreign: Some(&snap.foreign), hub: self.hub, vals: None };
                let truth = ev.truth(snap.model.actual, env, body)?;
                if mode == KMode::Knows {
                    Ok(Value::Bool(believes && truth))
                } else {
                    let disbelieves = foreign::believes_not(self.prog, tw, &st, env, body);
                    Ok(Value::Bool((believes && truth) || (disbelieves && !truth)))
                }
            }
        }
    }

    /// If a formula is about another world's facts, which world.
    pub fn foreign_world(&self, body: &E) -> R<Option<usize>> {
        let mut names = Vec::new();
        fact_names(body, &mut names);
        let world = self.world();
        let mut found: Option<usize> = None;
        for n in names {
            if world.facts.contains_key(&n) {
                continue;
            }
            for &o in &world.about {
                if self.prog.worlds[o].facts.contains_key(&n) {
                    if let Some(f) = found {
                        if f != o {
                            return Err("a belief can't mix facts from different worlds".into());
                        }
                    }
                    found = Some(o);
                }
            }
        }
        Ok(found)
    }

    fn static_type(&self, e: &E) -> Option<Ty> {
        let world = self.world();
        match &e.kind {
            ExprKind::Name(n) | ExprKind::Call(n, _) => world.facts.get(n).map(|f| f.ty.clone()),
            _ => None,
        }
    }

    pub fn type_domain(&self, t: &TypeRef) -> R<Vec<Value>> {
        let world = self.world();
        let ty = resolve_ty(world, t, &self.prog.params, 0).map_err(|e| e.1)?;
        domain_of(world, &ty).ok_or("that type has no finite domain".into())
    }
}

pub fn coerce(w: &World, ty: &Ty, v: Value) -> Value {
    match (ty, &v) {
        (Ty::Group(g), Value::Int(k)) if g != "Agent" => {
            let nm = format!("{}[{}]", g, k);
            w.agent_names.get(&nm).map(|a| Value::Agent(w.id as u16, *a)).unwrap_or(v)
        }
        _ => v,
    }
}

/// Names that look like fact references in a formula (unbound names and calls).
pub fn fact_names(e: &E, out: &mut Vec<String>) {
    match &e.kind {
        ExprKind::Name(n) => out.push(n.clone()),
        ExprKind::Call(n, args) => {
            out.push(n.clone());
            args.iter().for_each(|a| fact_names(a, out));
        }
        ExprKind::Field(b, _) => fact_names(b, out),
        ExprKind::Tuple(xs) => xs.iter().for_each(|x| fact_names(x, out)),
        ExprKind::Not(a) | ExprKind::Neg(a) => fact_names(a, out),
        ExprKind::Bin(_, a, b) => {
            fact_names(a, out);
            fact_names(b, out);
        }
        ExprKind::Quant { body, .. } => fact_names(body, out),
        ExprKind::Index(_, i) => fact_names(i, out),
        _ => {}
    }
}

/// Resolve a time reference to (world, step index).
pub fn resolve_time(prog: &Program, wid: usize, t: &TimeRef, hub: &dyn Hub, params: &std::collections::HashMap<String, i64>) -> R<(usize, usize)> {
    match t {
        TimeRef::Start => Ok((wid, 0)),
        TimeRef::End => {
            let n = hub.n_steps(wid).unwrap_or(prog.worlds[wid].steps.len());
            Ok((wid, n.saturating_sub(1)))
        }
        TimeRef::Before(inner) => {
            let (w, s) = resolve_time(prog, wid, inner, hub, params)?;
            if s == 0 {
                return Err("nothing comes before start".into());
            }
            Ok((w, s - 1))
        }
        TimeRef::Event { world, label, args } => {
            let label = if args.is_empty() {
                label.clone()
            } else {
                let vs = args.iter().map(|a| const_int(a, params, &vec![]).map(|x| x.to_string()).map_err(|e| e.1)).collect::<R<Vec<_>>>()?;
                format!("{}({})", label, vs.join(", "))
            };
            let candidates: Vec<usize> = match world {
                Some(wn) => vec![prog.world_by_name(wn).ok_or(format!("unknown world '{}'", wn))?],
                None => {
                    let mut c = vec![wid];
                    c.extend(prog.worlds[wid].about.iter().copied());
                    c
                }
            };
            for c in candidates {
                if label == "end" && world.is_some() {
                    let n = hub.n_steps(c).unwrap_or(prog.worlds[c].steps.len());
                    return Ok((c, n.saturating_sub(1)));
                }
                if let Some(i) = prog.worlds[c].label_index.get(&label) {
                    return Ok((c, *i));
                }
            }
            Err(format!("no event '{}'", label))
        }
    }
}
