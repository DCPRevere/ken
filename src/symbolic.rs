//! Symbolic engine: possible worlds as a BDD (a "knowledge structure").
//!
//! Applies to worlds built only from public events: everyone sees every event
//! after `start`, and each agent's starting knowledge is "which facts I can
//! see". Then the set of possible worlds is one boolean formula θ, and
//! "a knows φ" is ∀(variables a can't see). (θ → φ). That scales to
//! Blue Eyes with a hundred islanders, where listing worlds cannot.

use crate::ast::*;
use crate::bdd::{Bdd, B, FALSE, TRUE};
use crate::engine::{InitState, Runner};
use crate::eval::{coerce, Hub};
use crate::state::*;
use crate::value::*;
use crate::world::*;
use std::collections::HashMap;
use std::rc::Rc;

pub enum SymErr {
    /// The world needs the explicit engine.
    Fallback(String),
    /// A genuine error in the story.
    Error(String),
}
use SymErr::*;

type SR<T> = Result<T, SymErr>;
type Dist = Vec<(Value, B)>;

#[derive(Clone)]
pub struct SymSnap {
    pub theta: B,
    pub vals: Rc<Vec<Value>>,
}

pub struct Sym<'a> {
    pub prog: &'a Program,
    pub wid: usize,
    pub bdd: Bdd,
    bits: HashMap<usize, Vec<u32>>,
    hidden: Vec<u32>, // per agent: var-set id of the variables they can't see
    single: Vec<Option<u32>>, // per agent: the one variable they can't see, if exactly one
    assign: Vec<bool>,
    theta: B,
    vals: Vec<Value>,
    pub snaps: Vec<SymSnap>,
    pub diags: Vec<Diag>,
    gc_floor: usize,
    /// Shortcuts on (default). KEN_NO_SHORTCUTS=1 turns them off for testing.
    fast: bool,
}

/// Static check: could this world be checked symbolically?
pub fn eligible(prog: &Program, wid: usize) -> Result<(), String> {
    let w = &prog.worlds[wid];
    if !w.segments.is_empty() {
        return Err("it has time travellers".into());
    }
    if !w.about.is_empty() {
        return Err("it is about another world".into());
    }
    for o in &prog.worlds {
        if o.id != wid && (o.about.contains(&wid) || o.agents.iter().any(|a| a.sees_all_of == Some(wid)) || o.revises.as_ref().map(|r| r.0) == Some(wid)) {
            return Err(format!("world {} refers to it", o.name));
        }
    }
    for r in &w.rules {
        if !matches!((&r.trigger, &r.then), (Trigger::After(_), RuleThen::Do(_))) {
            return Err(format!("rule {} concludes or depends on what someone sees", r.name));
        }
    }
    for (t, st) in w.steps.iter().enumerate() {
        if !st.conclusions.is_empty() {
            return Err(format!("{} has conclusions", st.label));
        }
        if t > 0 && st.seen_by.is_some() {
            return Err(format!("{} has its own `seen by`", st.label));
        }
        if st.actions.iter().any(|c| c.name == "tell") {
            return Err(format!("{} uses tell", st.label));
        }
        if t == 0 {
            for it in st.seen_by.iter().flatten() {
                for m in &it.mods {
                    match m {
                        Modifier::Hiding(e) if !matches!(e.kind, ExprKind::Field(..)) => {}
                        _ => return Err("start uses `as`, `secretly` or hides part of a fact".into()),
                    }
                }
            }
        }
    }
    Ok(())
}

impl<'a> Sym<'a> {
    pub fn run(prog: &'a Program, wid: usize, hub: &dyn Hub) -> SR<Sym<'a>> {
        eligible(prog, wid).map_err(Fallback)?;
        let world = &prog.worlds[wid];
        let runner = Runner { prog, wid, hub, seg_beliefs: HashMap::new(), suppress: None };
        let InitState { truth, obs, varying } = runner.initial_state().map_err(Error)?;
        let mut bdd = Bdd::new();
        let mut bits: HashMap<usize, Vec<u32>> = HashMap::new();
        let mut next: u32 = 0;
        let mut assign: Vec<bool> = vec![];
        let mut theta = TRUE;
        for &s in &varying {
            let dom = &world.slots[s].domain;
            let d = dom.len().max(1);
            let nb = (usize::BITS - (d - 1).leading_zeros()).max(1) as usize;
            let vs: Vec<u32> = (0..nb as u32).map(|i| next + i).collect();
            next += nb as u32;
            let k = dom.iter().position(|v| *v == truth[s]).unwrap_or(0);
            for i in 0..nb {
                assign.push((k >> i) & 1 == 1);
            }
            bits.insert(s, vs);
            // codes beyond the domain are impossible
            for code in d..(1usize << nb) {
                let c = code_eq(&mut bdd, &bits[&s], code);
                let nc = bdd.not(c);
                theta = bdd.and(theta, nc);
            }
        }
        let na = world.agents.len();
        let mut hidden = vec![];
        let mut single = vec![];
        for a in 0..na {
            let mut hv = vec![];
            for &s in &varying {
                let sees = match &obs[a] {
                    None => false,
                    Some(h) => !h.iter().any(|(hs, _)| *hs == s),
                };
                if !sees {
                    hv.extend(bits[&s].iter().copied());
                }
            }
            single.push(if hv.len() == 1 { Some(hv[0]) } else { None });
            hidden.push(bdd.var_set(&hv));
        }
        let mut sym = Sym { prog, wid, bdd, bits, hidden, single, assign, theta, vals: truth, snaps: vec![], diags: vec![], gc_floor: 0, fast: std::env::var("KEN_NO_SHORTCUTS").is_err() };
        sym.snaps.push(SymSnap { theta: sym.theta, vals: Rc::new(sym.vals.clone()) });
        let timing = std::env::var("KEN_TIMING").is_ok();
        for t in 1..world.steps.len() {
            let t0 = std::time::Instant::now();
            sym.step(t)?;
            if timing {
                eprintln!("step {:>12} {:>8.1}ms  nodes {}", world.steps[t].label, t0.elapsed().as_secs_f64() * 1e3, sym.bdd.node_count());
            }
            sym.snaps.push(SymSnap { theta: sym.theta, vals: Rc::new(sym.vals.clone()) });
            sym.maybe_gc();
        }
        Ok(sym)
    }

    fn world(&self) -> &'a World {
        &self.prog.worlds[self.wid]
    }

    /// Collect garbage when the node table has doubled since the last collection.
    fn maybe_gc(&mut self) {
        if self.bdd.node_count() < 2 * self.gc_floor.max(250_000) {
            return;
        }
        let mut roots: Vec<B> = vec![self.theta];
        roots.extend(self.snaps.iter().map(|s| s.theta));
        let r = self.bdd.gc(&roots);
        self.theta = r[0];
        for (s, t) in self.snaps.iter_mut().zip(r[1..].iter()) {
            s.theta = *t;
        }
        self.gc_floor = self.bdd.node_count();
    }

    fn diag(&mut self, t: usize, msg: String) {
        let w = self.world();
        self.diags.push(Diag { level: Level::Error, line: w.steps[t].span.line, world: w.name.clone(), at: Some(w.steps[t].label.clone()), msg });
    }

    fn holds(&self, f: B) -> bool {
        self.bdd.eval(f, &self.assign)
    }

    fn instantiate(&mut self, c: &Call, env: &Env) -> SR<ActionInst> {
        let w = self.world();
        let info = w.actions.get(&c.name).ok_or_else(|| Error(format!("unknown action '{}'", c.name)))?;
        if info.params.len() != c.args.len() {
            return Err(Error(format!("{} takes {} argument(s)", c.name, info.params.len())));
        }
        let mut args = vec![];
        for ((_, ty), e) in info.params.iter().zip(c.args.iter()) {
            if *ty == Ty::Content {
                args.push(Value::Formula(Rc::new(FormulaVal { expr: e.clone(), env: env.clone(), world: self.wid })));
            } else {
                let v = self.concrete(e, env)?;
                args.push(coerce(w, ty, v));
            }
        }
        Ok(ActionInst { name: Rc::from(c.name.as_str()), args })
    }

    fn concrete(&mut self, e: &E, env: &Env) -> SR<Value> {
        let d = self.term(e, env)?;
        let live: Vec<Value> = {
            let mut out = vec![];
            for (v, c) in d {
                let x = self.bdd.and(c, self.theta);
                if x != FALSE {
                    out.push(v);
                }
            }
            out
        };
        match live.len() {
            1 => Ok(live.into_iter().next().unwrap()),
            0 => Err(Error(format!("`{}` has no possible value", self.prog.text(e.span)))),
            _ => Err(Fallback(format!("`{}` differs between possible worlds", self.prog.text(e.span)))),
        }
    }

    fn action_env(&self, a: &ActionInst) -> Env {
        let info = &self.world().actions[&*a.name];
        info.params.iter().zip(a.args.iter()).map(|((n, _), v)| (Rc::from(n.as_str()), v.clone())).collect()
    }

    fn require_public(&self, a: &ActionInst) -> SR<()> {
        let info = &self.world().actions[&*a.name];
        match &info.seen_by {
            Some(items) if items.len() == 1 && matches!(items[0].who, Who::Everyone) && items[0].mods.is_empty() => Ok(()),
            _ => Err(Fallback(format!("{} is not seen by everyone", a.name))),
        }
    }

    fn apply_effects(&mut self, act: &ActionInst) -> SR<()> {
        let w = self.world();
        let info = &w.actions[&*act.name];
        let env = self.action_env(act);
        for eff in &info.effects.clone() {
            let slot = self.slot_of(&eff.target, &env)?;
            if self.bits.contains_key(&slot) {
                return Err(Fallback("an event changes a fact that differs between possible worlds".into()));
            }
            let v = self.concrete(&eff.value, &env)?;
            self.vals[slot] = coerce(w, &w.facts[&w.slots[slot].fact].ty, v);
        }
        Ok(())
    }

    fn slot_of(&mut self, e: &E, env: &Env) -> SR<usize> {
        let w = self.world();
        let (name, args): (&String, Vec<E>) = match &e.kind {
            ExprKind::Name(n) => (n, vec![]),
            ExprKind::Call(n, a) => (n, a.clone()),
            _ => return Err(Error(format!("'{}' is not a fact", self.prog.text(e.span)))),
        };
        let f = w.facts.get(name).ok_or_else(|| Error(format!("unknown fact '{}'", name)))?;
        let mut vs = vec![];
        for (a, t) in args.iter().zip(f.params.clone().iter()) {
            let v = self.concrete(a, env)?;
            vs.push(coerce(w, t, v));
        }
        w.slot_of.get(&(name.clone(), vs)).copied().ok_or_else(|| Error(format!("'{}' is not a valid fact", self.prog.text(e.span))))
    }

    fn step(&mut self, t: usize) -> SR<()> {
        let w = self.world();
        let st = &w.steps[t];
        let mut actions = vec![];
        for c in &st.actions {
            let a = self.instantiate(c, &st.env)?;
            self.require_public(&a)?;
            actions.push(a);
        }
        if let Some(b) = &st.because {
            let f = self.form(b, &st.env)?;
            if !self.holds(f) {
                self.diag(t, format!("this happens because `{}`, but that isn't true just before {}", self.prog.text(b.span), st.label));
            }
        }
        // public preconditions: everyone learns they held
        let mut pres = vec![];
        for act in &actions {
            let info = &w.actions[&*act.name];
            let env = self.action_env(act);
            for n in &info.needs {
                let f = self.form(n, &env)?;
                if !self.holds(f) {
                    self.diag(t, format!("{} needs `{}`, which is false here", self.prog.show_action(act), self.prog.text(n.span)));
                } else {
                    pres.push(f);
                }
            }
        }
        for f in pres {
            self.theta = self.bdd.and(self.theta, f);
        }
        for act in &actions {
            self.apply_effects(act)?;
        }
        // rules fire in every world; everyone sees what fired, and what didn't
        let tc = std::time::Instant::now();
        let mut fired: Vec<(B, bool, Call, Env)> = vec![];
        // "i knows their own hidden bit": those who didn't act are combined in one pass
        let mut still: Vec<u32> = vec![];
        for r in &w.rules {
            let (Trigger::After(pat), RuleThen::Do(call)) = (&r.trigger, &r.then) else { continue };
            for act in &actions {
                let Some(env) = self.match_pattern(pat, act)? else { continue };
                let envs: Vec<Env> = match &r.for_every {
                    Some((g, var)) => w.groups.get(g).ok_or_else(|| Error(format!("unknown group '{}'", g)))?.iter().map(|a| env_with(&env, var, Value::Agent(self.wid as u16, *a))).collect(),
                    None => vec![env],
                };
                for e2 in envs {
                    if let (true, Some(cond)) = (self.fast, &r.when) {
                        if let Some((x, rest)) = self.knows_own_bit(cond, &e2)? {
                            if rest == FALSE {
                                continue; // can't fire anywhere: nothing to observe
                            }
                            if rest == TRUE {
                                // knows x at the actual world iff flipping x leaves θ
                                let mut flipped = self.assign.clone();
                                flipped[x as usize] = !flipped[x as usize];
                                let now = !self.bdd.eval(self.theta, &flipped);
                                if now {
                                    let set = self.bdd.var_set(&[x]);
                                    let stay = self.bdd.forall(self.theta, set);
                                    fired.push((stay ^ 1, true, call.clone(), e2));
                                } else {
                                    still.push(x);
                                }
                                continue;
                            }
                        }
                    }
                    let c = match &r.when {
                        Some(cond) => self.form(cond, &e2)?,
                        None => TRUE,
                    };
                    let now = self.holds(c);
                    fired.push((c, now, call.clone(), e2));
                }
            }
        }
        let t_cond = tc.elapsed();
        let tt = std::time::Instant::now();
        let mut triggered = vec![];
        if !still.is_empty() {
            let set = self.bdd.var_set(&still);
            let stay = self.bdd.forall_each(self.theta, set);
            self.theta = self.bdd.and(self.theta, stay);
        }
        for (c, now, call, env) in &fired {
            let obs = if *now { *c } else { self.bdd.not(*c) };
            self.theta = self.bdd.and(self.theta, obs);
            if *now {
                triggered.push((call.clone(), env.clone()));
            }
        }
        if std::env::var("KEN_TIMING").is_ok() && !fired.is_empty() {
            eprintln!("   conditions {:.1}ms  theta-updates {:.1}ms  |theta|={}", t_cond.as_secs_f64() * 1e3, tt.elapsed().as_secs_f64() * 1e3, self.size(self.theta));
        }
        for (call, env) in triggered {
            let act = self.instantiate(&call, &env)?;
            self.require_public(&act)?;
            let info = &w.actions[&*act.name];
            let aenv = self.action_env(&act);
            for n in &info.needs {
                let f = self.form(n, &aenv)?;
                if !self.holds(f) {
                    self.diag(t, format!("{} needs `{}`, which is false here", self.prog.show_action(&act), self.prog.text(n.span)));
                }
            }
            self.apply_effects(&act)?;
        }
        Ok(())
    }

    fn match_pattern(&mut self, pat: &Call, act: &ActionInst) -> SR<Option<Env>> {
        if pat.name != *act.name || pat.args.len() != act.args.len() {
            return Ok(None);
        }
        let w = self.world();
        let mut env: Env = vec![];
        for (p, v) in pat.args.iter().zip(act.args.iter()) {
            if let ExprKind::Name(n) = &p.kind {
                let bound = w.facts.contains_key(n) || w.agent_names.contains_key(n) || w.consts.contains_key(n) || self.prog.params.contains_key(n);
                if !bound {
                    match env_get(&env, n) {
                        Some(prev) if prev != v => return Ok(None),
                        Some(_) => {}
                        None => env.push((Rc::from(n.as_str()), v.clone())),
                    }
                    continue;
                }
            }
            if self.concrete(p, &env)? != *v {
                return Ok(None);
            }
        }
        Ok(Some(env))
    }

    // ------------------------------------------------------------ evaluation

    fn size(&self, f: B) -> usize {
        self.bdd.size(f)
    }

    /// Recognise `a knows <a's own hidden one-bit fact> [and <cheap condition>]`.
    /// Returns the bit and the cheap condition's value.
    fn knows_own_bit(&mut self, cond: &E, env: &Env) -> SR<Option<(u32, B)>> {
        let (k, rest) = match &cond.kind {
            ExprKind::Epistemic { .. } => (cond, None),
            ExprKind::Bin(BinOp::And, a, b) if matches!(a.kind, ExprKind::Epistemic { .. }) && !has_beliefs(b) => (a, Some(b)),
            ExprKind::Bin(BinOp::And, a, b) if matches!(b.kind, ExprKind::Epistemic { .. }) && !has_beliefs(a) => (b, Some(a)),
            _ => return Ok(None),
        };
        let ExprKind::Epistemic { agent, mode, body } = &k.kind else { return Ok(None) };
        let a = self.agent(agent, env)?;
        let Some(x) = self.single[a as usize] else { return Ok(None) };
        let slot = match &body.kind {
            ExprKind::Name(_) | ExprKind::Call(..) => match self.slot_of(body, env) {
                Ok(s) => s,
                Err(_) => return Ok(None),
            },
            _ => return Ok(None),
        };
        if self.bits.get(&slot).map(|b| b.as_slice()) != Some(&[x][..]) {
            return Ok(None);
        }
        let is_bool = self.world().slots[slot].domain.first() == Some(&Value::Bool(false));
        // knowing the value: `knows <non-bool fact>` or `knows whether <bool fact>`
        let value_knowledge = (*mode == KMode::Knows && !is_bool) || (*mode == KMode::KnowsWhether && is_bool);
        if !value_knowledge {
            return Ok(None);
        }
        let rest = match rest {
            Some(r) => self.form(r, env)?,
            None => TRUE,
        };
        Ok(Some((x, rest)))
    }

    /// "a knows φ" as a BDD: true in every possible world that looks the same to a.
    fn k(&mut self, a: u32, f: B) -> B {
        if let (true, Some(x)) = (self.fast, self.single[a as usize]) {
            // blind to exactly one variable: K f = (θ|x=0 → f|x=0) ∧ (θ|x=1 → f|x=1)
            let t0 = self.bdd.restrict(self.theta, x, false);
            let t1 = self.bdd.restrict(self.theta, x, true);
            let f0 = self.bdd.restrict(f, x, false);
            let f1 = self.bdd.restrict(f, x, true);
            let a0 = self.bdd.implies(t0, f0);
            let a1 = self.bdd.implies(t1, f1);
            return self.bdd.and(a0, a1);
        }
        let imp = self.bdd.implies(self.theta, f);
        self.bdd.forall(imp, self.hidden[a as usize])
    }

    /// ∧ over agents of "a knows f". One pass when each is blind to a single,
    /// distinct variable.
    fn k_all(&mut self, agents: &[u32], f: B) -> B {
        let singles: Option<Vec<u32>> = agents.iter().map(|a| self.single[*a as usize]).collect();
        if let (true, Some(vs)) = (self.fast, singles) {
            let mut sorted = vs.clone();
            sorted.sort_unstable();
            sorted.dedup();
            if sorted.len() == vs.len() && !vs.is_empty() {
                let imp = self.bdd.implies(self.theta, f);
                let set = self.bdd.var_set(&vs);
                return self.bdd.forall_each(imp, set);
            }
        }
        let mut acc = TRUE;
        for &a in agents {
            let ka = self.k(a, f);
            acc = self.bdd.and(acc, ka);
        }
        acc
    }

    fn possible(&mut self, a: u32, f: B) -> B {
        let x = self.bdd.and(self.theta, f);
        self.bdd.exists(x, self.hidden[a as usize])
    }

    fn agent(&mut self, e: &E, env: &Env) -> SR<u32> {
        match self.concrete(e, env)? {
            Value::Agent(w, a) if w as usize == self.wid => Ok(a),
            v => Err(Error(format!("'{}' is {}, not an agent", self.prog.text(e.span), self.prog.show(&v)))),
        }
    }

    fn truth_of(&mut self, d: Dist) -> SR<B> {
        let mut f = FALSE;
        for (v, c) in d {
            match v {
                Value::Bool(true) => f = self.bdd.or(f, c),
                Value::Bool(false) => {}
                other => return Err(Error(format!("{} is not true or false", self.prog.show(&other)))),
            }
        }
        Ok(f)
    }

    pub fn form(&mut self, e: &E, env: &Env) -> SR<B> {
        match &e.kind {
            ExprKind::Bool(b) => Ok(if *b { TRUE } else { FALSE }),
            ExprKind::Not(a) => {
                let f = self.form(a, env)?;
                Ok(self.bdd.not(f))
            }
            ExprKind::Bin(op @ (BinOp::And | BinOp::Or), a, b) => {
                // cheap side first; skip the other when it decides the answer
                let (first, second) = if has_beliefs(a) && !has_beliefs(b) { (b, a) } else { (a, b) };
                let x = self.form(first, env)?;
                let decided = if *op == BinOp::And { FALSE } else { TRUE };
                if x == decided {
                    return Ok(decided);
                }
                let y = self.form(second, env)?;
                Ok(if *op == BinOp::And { self.bdd.and(x, y) } else { self.bdd.or(x, y) })
            }
            ExprKind::Bin(op @ (BinOp::Implies | BinOp::Iff), a, b) => {
                let x = self.form(a, env)?;
                if *op == BinOp::Implies && x == FALSE {
                    return Ok(TRUE);
                }
                let y = self.form(b, env)?;
                Ok(match op {
                    BinOp::And => self.bdd.and(x, y),
                    BinOp::Or => self.bdd.or(x, y),
                    BinOp::Implies => self.bdd.implies(x, y),
                    _ => self.bdd.iff(x, y),
                })
            }
            ExprKind::Quant { all, var, ty, body } => {
                let w = self.world();
                let t = resolve_ty(w, ty, &self.prog.params, e.span.line).map_err(|x| Error(x.1))?;
                let dom = domain_of(w, &t).ok_or_else(|| Error("that type has no finite domain".into()))?;
                let mut acc = if *all { TRUE } else { FALSE };
                for v in dom {
                    let f = self.form(body, &env_with(env, var, v))?;
                    acc = if *all { self.bdd.and(acc, f) } else { self.bdd.or(acc, f) };
                }
                Ok(acc)
            }
            ExprKind::Epistemic { agent, mode, body } => {
                let a = self.agent(agent, env)?;
                let d = self.term(body, env)?;
                let is_bool = d.iter().all(|(v, _)| matches!(v, Value::Bool(_)));
                if is_bool {
                    let f = self.truth_of(d)?;
                    Ok(match mode {
                        KMode::Knows | KMode::Believes => self.k(a, f),
                        KMode::KnowsWhether => {
                            let nf = self.bdd.not(f);
                            let x = self.k(a, f);
                            let y = self.k(a, nf);
                            self.bdd.or(x, y)
                        }
                    })
                } else {
                    // knows the value: for some value, knows it is that value
                    let mut acc = FALSE;
                    for (_, c) in d {
                        let kc = self.k(a, c);
                        acc = self.bdd.or(acc, kc);
                    }
                    Ok(acc)
                }
            }
            ExprKind::Common { group, body } => {
                let w = self.world();
                let members: Vec<u32> = match group {
                    Some(g) => w.groups.get(g).cloned().ok_or_else(|| Error(format!("unknown group '{}'", g)))?,
                    None => w.groups["Agent"].clone(),
                };
                let f = self.form(body, env)?;
                let mut x = TRUE;
                loop {
                    let fx = self.bdd.and(f, x);
                    let y = self.k_all(&members, fx);
                    let y = self.bdd.and(y, self.theta);
                    let xt = self.bdd.and(x, self.theta);
                    if y == xt {
                        return Ok(y);
                    }
                    x = y;
                }
            }
            ExprKind::Deducible { agent, body } => {
                let a = self.agent(agent, env)?;
                let f = self.form(body, env)?;
                Ok(self.k(a, f))
            }
            ExprKind::Possible { agent, body } => {
                let a = self.agent(agent, env)?;
                let f = self.form(body, env)?;
                Ok(self.possible(a, f))
            }
            ExprKind::At(inner, t) => {
                let s = self.local_step(t)?;
                let snap = self.snaps.get(s).cloned().ok_or_else(|| Error("that time hasn't been reached".into()))?;
                let (th, vs) = (self.theta, std::mem::replace(&mut self.vals, (*snap.vals).clone()));
                self.theta = snap.theta;
                let r = self.form(inner, env);
                self.theta = th;
                self.vals = vs;
                let f = r?;
                Ok(if self.holds(f) { TRUE } else { FALSE })
            }
            ExprKind::Saw { .. } | ExprKind::SeenAs { .. } => Err(Fallback("`saw` needs the explicit engine".into())),
            _ => {
                let d = self.term(e, env)?;
                self.truth_of(d)
            }
        }
    }

    fn local_step(&self, t: &TimeRef) -> SR<usize> {
        let w = self.world();
        Ok(match t {
            TimeRef::Start => 0,
            TimeRef::End => w.steps.len() - 1,
            TimeRef::Before(inner) => self.local_step(inner)?.checked_sub(1).ok_or_else(|| Error("nothing comes before start".into()))?,
            TimeRef::Event { world: None, label, args } => {
                let label = if args.is_empty() {
                    label.clone()
                } else {
                    let vs = args.iter().map(|a| const_int(a, &self.prog.params, &vec![]).map(|x| x.to_string()).map_err(|e| Error(e.1))).collect::<SR<Vec<_>>>()?;
                    format!("{}({})", label, vs.join(", "))
                };
                *w.label_index.get(&label).ok_or_else(|| Error(format!("no event '{}'", label)))?
            }
            _ => return Err(Fallback("references to other worlds need the explicit engine".into())),
        })
    }

    /// A term as a distribution: each possible value with the worlds where it holds.
    fn term(&mut self, e: &E, env: &Env) -> SR<Dist> {
        let w = self.world();
        let c = |v: Value| Ok(vec![(v, TRUE)]);
        match &e.kind {
            ExprKind::Int(n) => c(Value::Int(*n)),
            ExprKind::Bool(b) => c(Value::Bool(*b)),
            ExprKind::Name(n) => {
                if let Some(v) = env_get(env, n) {
                    if let Value::Formula(f) = v {
                        let f = f.clone();
                        let b = self.form(&f.expr, &f.env)?;
                        return Ok(self.bool_dist(b));
                    }
                    return c(v.clone());
                }
                if let Some(v) = self.prog.params.get(n) {
                    return c(Value::Int(*v));
                }
                if w.facts.contains_key(n) {
                    let s = w.slot_of.get(&(n.clone(), vec![])).copied().ok_or_else(|| Error(format!("'{}' takes arguments", n)))?;
                    return Ok(self.slot_dist(s));
                }
                if let Some(a) = w.agent_names.get(n) {
                    return c(Value::Agent(self.wid as u16, *a));
                }
                if w.consts.contains_key(n) {
                    return c(Value::Sym(Rc::from(n.as_str())));
                }
                if w.label_index.contains_key(n) {
                    return Err(Fallback("events as values need the explicit engine".into()));
                }
                Err(Error(format!("unknown name '{}'", n)))
            }
            ExprKind::Call(n, args) => {
                let f = w.facts.get(n).ok_or_else(|| Error(format!("unknown fact '{}'", n)))?.clone();
                if f.params.len() != args.len() {
                    return Err(Error(format!("'{}' takes {} argument(s)", n, f.params.len())));
                }
                let mut combos: Vec<(Vec<Value>, B)> = vec![(vec![], TRUE)];
                for (a, t) in args.iter().zip(f.params.iter()) {
                    let d = self.term(a, env)?;
                    let mut next = vec![];
                    for (vs, cc) in &combos {
                        for (v, c2) in &d {
                            let cond = self.bdd.and(*cc, *c2);
                            if cond == FALSE {
                                continue;
                            }
                            let mut vs2 = vs.clone();
                            vs2.push(coerce(w, t, v.clone()));
                            next.push((vs2, cond));
                        }
                    }
                    combos = next;
                }
                let mut out: Dist = vec![];
                for (vs, cc) in combos {
                    let s = *w.slot_of.get(&(n.clone(), vs)).ok_or_else(|| Error(format!("'{}' is not a valid fact", self.prog.text(e.span))))?;
                    for (v, c2) in self.slot_dist(s) {
                        let cond = self.bdd.and(cc, c2);
                        out.push((v, cond));
                    }
                }
                Ok(self.merge(out))
            }
            ExprKind::Index(g, i) => match self.concrete(i, env)? {
                Value::Int(k) => {
                    let nm = format!("{}[{}]", g, k);
                    w.agent_names.get(&nm).map(|a| vec![(Value::Agent(self.wid as u16, *a), TRUE)]).ok_or_else(|| Error(format!("no agent {}", nm)))
                }
                _ => Err(Error("an index must be a number".into())),
            },
            ExprKind::Field(b, f) => {
                let ty = match &b.kind {
                    ExprKind::Name(n) | ExprKind::Call(n, _) => w.facts.get(n).map(|x| x.ty.clone()),
                    _ => None,
                };
                let Some(Ty::Record(_, fs)) = ty else { return Err(Error(format!("'{}' has no fields", self.prog.text(b.span)))) };
                let i = fs.iter().position(|(n, _)| n == f).ok_or_else(|| Error(format!("no field '{}'", f)))?;
                let d = self.term(b, env)?;
                let out = d
                    .into_iter()
                    .map(|(v, cc)| match v {
                        Value::Tuple(xs) => (xs[i].clone(), cc),
                        other => (other, cc),
                    })
                    .collect();
                Ok(self.merge(out))
            }
            ExprKind::Tuple(xs) => {
                let mut combos: Vec<(Vec<Value>, B)> = vec![(vec![], TRUE)];
                for x in xs {
                    let d = self.term(x, env)?;
                    let mut next = vec![];
                    for (vs, cc) in &combos {
                        for (v, c2) in &d {
                            let cond = self.bdd.and(*cc, *c2);
                            if cond != FALSE {
                                let mut vs2 = vs.clone();
                                vs2.push(v.clone());
                                next.push((vs2, cond));
                            }
                        }
                    }
                    combos = next;
                }
                Ok(combos.into_iter().map(|(vs, cc)| (Value::Tuple(vs.into()), cc)).collect())
            }
            ExprKind::Neg(a) => {
                let d = self.term(a, env)?;
                d.into_iter().map(|(v, cc)| match v {
                    Value::Int(n) => Ok((Value::Int(-n), cc)),
                    _ => Err(Error("expected a number".into())),
                }).collect()
            }
            ExprKind::Bin(op @ (BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Add | BinOp::Sub | BinOp::Mul), a, b) => {
                let x = self.term(a, env)?;
                let y = self.term(b, env)?;
                let mut out: Dist = vec![];
                for (v1, c1) in &x {
                    for (v2, c2) in &y {
                        let cond = self.bdd.and(*c1, *c2);
                        if cond == FALSE {
                            continue;
                        }
                        let r = match op {
                            BinOp::Eq => Value::Bool(v1 == v2),
                            BinOp::Ne => Value::Bool(v1 != v2),
                            _ => {
                                let (Value::Int(p), Value::Int(q)) = (v1, v2) else { return Err(Error("expected numbers".into())) };
                                match op {
                                    BinOp::Lt => Value::Bool(p < q),
                                    BinOp::Le => Value::Bool(p <= q),
                                    BinOp::Gt => Value::Bool(p > q),
                                    BinOp::Ge => Value::Bool(p >= q),
                                    BinOp::Add => Value::Int(p + q),
                                    BinOp::Sub => Value::Int(p - q),
                                    _ => Value::Int(p * q),
                                }
                            }
                        };
                        out.push((r, cond));
                    }
                }
                Ok(self.merge(out))
            }
            ExprKind::Qualified(..) => Err(Fallback("references to other worlds need the explicit engine".into())),
            _ => {
                let b = self.form(e, env)?;
                Ok(self.bool_dist(b))
            }
        }
    }

    fn bool_dist(&mut self, b: B) -> Dist {
        let nb = self.bdd.not(b);
        vec![(Value::Bool(true), b), (Value::Bool(false), nb)]
    }

    fn slot_dist(&mut self, s: usize) -> Dist {
        match self.bits.get(&s).cloned() {
            None => vec![(self.vals[s].clone(), TRUE)],
            Some(bs) => {
                let dom = self.world().slots[s].domain.clone();
                dom.into_iter().enumerate().map(|(k, v)| (v, code_eq(&mut self.bdd, &bs, k))).collect()
            }
        }
    }

    fn merge(&mut self, d: Dist) -> Dist {
        let mut out: Dist = vec![];
        for (v, c) in d {
            if let Some(slot) = out.iter_mut().find(|(x, _)| *x == v) {
                slot.1 = self.bdd.or(slot.1, c);
            } else {
                out.push((v, c));
            }
        }
        out
    }

    /// Evaluate a formula at a recorded step, in the actual world.
    pub fn eval_at(&mut self, step: usize, f: &E) -> SR<bool> {
        let t0 = std::time::Instant::now();
        let r = self.eval_at_inner(step, f);
        if std::env::var("KEN_TIMING").is_ok() {
            eprintln!("expect {:>40} {:>8.1}ms", self.prog.text(f.span).chars().take(40).collect::<String>(), t0.elapsed().as_secs_f64() * 1e3);
        }
        r
    }

    fn eval_at_inner(&mut self, step: usize, f: &E) -> SR<bool> {
        let snap = self.snaps[step].clone();
        let (th, vs) = (self.theta, std::mem::replace(&mut self.vals, (*snap.vals).clone()));
        self.theta = snap.theta;
        let r = self.form(f, &vec![]);
        self.theta = th;
        self.vals = vs;
        Ok(self.holds(r?))
    }
}

/// Does a formula mention anyone's knowledge? (Those parts are the expensive ones.)
fn has_beliefs(e: &E) -> bool {
    match &e.kind {
        ExprKind::Epistemic { .. } | ExprKind::Common { .. } | ExprKind::Deducible { .. } | ExprKind::Possible { .. } => true,
        ExprKind::Not(a) | ExprKind::Neg(a) | ExprKind::Field(a, _) | ExprKind::At(a, _) | ExprKind::Index(_, a) => has_beliefs(a),
        ExprKind::Bin(_, a, b) => has_beliefs(a) || has_beliefs(b),
        ExprKind::Quant { body, .. } => has_beliefs(body),
        ExprKind::Call(_, xs) | ExprKind::Tuple(xs) => xs.iter().any(has_beliefs),
        _ => false,
    }
}

fn code_eq(bdd: &mut Bdd, bits: &[u32], code: usize) -> B {
    let mut f = TRUE;
    for (i, &v) in bits.iter().enumerate() {
        let x = bdd.var(v);
        let lit = if (code >> i) & 1 == 1 { x } else { bdd.not(x) };
        f = bdd.and(f, lit);
    }
    f
}
