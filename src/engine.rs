//! Running one world's timeline.

use crate::ast::*;
use crate::eval::*;
use crate::foreign;
use crate::kripke::{contract, product, Model, Scenarios};
use crate::state::*;
use crate::value::*;
use crate::world::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
    F(Value),
    Slot(usize, Value),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Scen {
    Skip,
    Ev(Rc<EvScen>),
    BelReal(u32, Rc<Vec<Constraint>>),
    BelImg(u32, Rc<Vec<Constraint>>),
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EvScen {
    pub actions: Vec<ActionInst>,
    pub step: Option<usize>,
    pub keep_secret: Option<u32>,
    pub filtered: bool,
    pub extra_pre: Vec<Value>,
    /// Perceived by a person: trusted testimony is taken at face value,
    /// without reasoning about how the teller knew.
    pub lenient: bool,
    /// The event's preconditions failed in reality (already reported):
    /// observers learn nothing from them.
    pub ignore_needs: bool,
}

#[derive(Clone, Debug)]
enum View {
    Full { secret: bool },
    Acts { acts: Vec<ActionInst>, step_clauses: bool, secret: bool },
}

pub struct Runner<'a> {
    pub prog: &'a Program,
    pub wid: usize,
    pub hub: &'a dyn Hub,
    pub seg_beliefs: HashMap<u32, Vec<(usize, Value)>>,
    pub suppress: Option<u32>,
}

pub struct InitState {
    pub truth: Vec<Value>,
    /// per agent: None = saw nothing; Some(hidden parts as (slot, field))
    pub obs: Vec<Option<Vec<(usize, Option<usize>)>>>,
    pub varying: Vec<usize>,
}

pub struct EventOut {
    pub model: Model,
    pub actual: Vec<ActionInst>,
    pub views: Vec<Option<Vec<ActionInst>>>,
    pub triggered_errors: Vec<String>,
}

struct PendingConcl {
    key: CKey,
    agent_expr: Option<E>,
    agent: Option<u32>,
    formula: E,
    env: Env,
    because: Option<E>,
    despite: Option<E>,
    line: usize,
}

impl<'a> Runner<'a> {
    pub fn world(&self) -> &'a World {
        &self.prog.worlds[self.wid]
    }

    fn ev<'b>(&'b self, m: &'b Model) -> Ev<'b> {
        Ev { prog: self.prog, wid: self.wid, model: m, step: 0, registry: None, foreign: None, hub: Some(self.hub), vals: None }
    }

    fn n_agents(&self) -> usize {
        self.world().agents.len()
    }

    // ------------------------------------------------------------ initial model

    /// Truth at start, what each agent observed of it, and which slots vary.
    pub fn initial_state(&self) -> Result<InitState, String> {
        let w = self.world();
        let start = &w.steps[0];
        let blank = Model { vals: vec![], rel: vec![], actual: 0 };
        let mut truth: Vec<Option<Value>> = vec![None; w.slots.len()];
        // defaults
        for (ix, s) in w.slots.iter().enumerate() {
            let f = &w.facts[&s.fact];
            if let Some(d) = &f.default {
                let vals: Vec<Value> = vec![Value::Unknown; w.slots.len()];
                let ev = Ev { vals: Some(&vals), ..self.ev(&blank) };
                truth[ix] = Some(ev.eval(0, &vec![], d)?);
            }
        }
        // assignments in start
        for a in &start.assigns {
            let mut envs: Vec<Env> = vec![start.env.clone()];
            if let Some((v, lo, hi)) = &a.for_range {
                let lo = const_int(lo, &self.prog.params, &start.env).map_err(|e| e.1)?;
                let hi = const_int(hi, &self.prog.params, &start.env).map_err(|e| e.1)?;
                envs = (lo..=hi).map(|k| env_with(&start.env, v, Value::Int(k))).collect();
            }
            for env in envs {
                let vals: Vec<Value> = truth.iter().map(|t| t.clone().unwrap_or(Value::Unknown)).collect();
                let ev = Ev { vals: Some(&vals), ..self.ev(&blank) };
                let slot = self.target_slot(&ev, 0, &env, &a.target).map_err(|m| format!("line {}: {}", a.span.line, m))?;
                let v = ev.eval(0, &env, &a.value).map_err(|m| format!("line {}: {}", a.span.line, m))?;
                let v = coerce(w, &w.facts[&w.slots[slot].fact].ty, v);
                if !w.slots[slot].domain.is_empty() && !w.slots[slot].domain.contains(&v) {
                    return Err(format!("line {}: {} can't be {}", a.span.line, self.slot_name(slot), self.prog.show(&v)));
                }
                truth[slot] = Some(v);
            }
        }
        let mut tv: Vec<Value> = Vec::with_capacity(w.slots.len());
        for (ix, t) in truth.iter().enumerate() {
            match t {
                Some(v) => tv.push(v.clone()),
                None => {
                    if w.relevant.contains(&ix) {
                        return Err(format!("{} is never given a value: set it in `start` or give the fact a default", self.slot_name(ix)));
                    }
                    tv.push(w.slots[ix].domain.first().cloned().unwrap_or(Value::Unknown));
                }
            }
        }
        // observations of the initial state
        let na = self.n_agents();
        // per agent: None = saw nothing; Some(hidden) where hidden = (slot, field)
        let mut obs: Vec<Option<Vec<(usize, Option<usize>)>>> = vec![None; na];
        if let Some(items) = &start.seen_by {
            let tm = Model { vals: vec![tv.clone().into()], rel: vec![vec![vec![0]]; na], actual: 0 };
            let ev = self.ev(&tm);
            for it in items {
                let agents = self.who(&ev, 0, &start.env, &it.who)?;
                for (a, env) in agents {
                    let mut hidden = obs[a as usize].take().unwrap_or_default();
                    for m in &it.mods {
                        match m {
                            Modifier::Hiding(e) => hidden.push(self.hidden_part(&ev, &env, e)?),
                            Modifier::Secretly => {}
                            Modifier::As(_) => return Err("`as` can't be used at start".into()),
                        }
                    }
                    obs[a as usize] = Some(hidden);
                }
            }
        }
        // which relevant slots vary
        let mut varying: Vec<usize> = Vec::new();
        let mut rel_slots: Vec<usize> = w.relevant.iter().copied().collect();
        rel_slots.sort_unstable();
        for &s in &rel_slots {
            let all_see = obs.iter().all(|o| match o {
                None => false,
                Some(h) => !h.iter().any(|(hs, _)| *hs == s),
            });
            if !all_see {
                varying.push(s);
            }
        }
        Ok(InitState { truth: tv, obs, varying })
    }

    pub fn initial(&self) -> Result<Model, String> {
        let w = self.world();
        let na = self.n_agents();
        let InitState { truth: tv, obs, varying } = self.initial_state()?;
        let mut count: usize = 1;
        for &s in &varying {
            count = count.saturating_mul(w.slots[s].domain.len().max(1));
        }
        if count > 500_000 {
            return Err(format!("{} possible starting worlds is too many; reduce what is hidden or the parameters", count));
        }
        let mut worlds: Vec<Vec<Value>> = vec![tv.clone()];
        let mut combos: Vec<Vec<Value>> = vec![vec![]];
        for &s in &varying {
            let mut next = Vec::new();
            for c in &combos {
                for v in &w.slots[s].domain {
                    let mut c2 = c.clone();
                    c2.push(v.clone());
                    next.push(c2);
                }
            }
            combos = next;
        }
        worlds.clear();
        let mut actual = 0;
        for c in combos {
            let mut v = tv.clone();
            for (i, &s) in varying.iter().enumerate() {
                v[s] = c[i].clone();
            }
            if varying.iter().all(|&s| v[s] == tv[s]) {
                actual = worlds.len();
            }
            worlds.push(v);
        }
        // relations from observation keys
        let mut rel = vec![vec![Vec::new(); worlds.len()]; na];
        for a in 0..na {
            let mut classes: HashMap<Vec<Value>, Vec<u32>> = HashMap::new();
            let mut keys = Vec::with_capacity(worlds.len());
            for (wi, v) in worlds.iter().enumerate() {
                let key: Vec<Value> = match &obs[a] {
                    None => vec![],
                    Some(hidden) => varying
                        .iter()
                        .map(|&s| match hidden.iter().find(|(hs, _)| *hs == s) {
                            None => v[s].clone(),
                            Some((_, None)) => Value::Unknown,
                            Some((_, Some(field))) => match &v[s] {
                                Value::Tuple(xs) => {
                                    let mut ys: Vec<Value> = xs.to_vec();
                                    ys[*field] = Value::Unknown;
                                    Value::Tuple(ys.into())
                                }
                                x => x.clone(),
                            },
                        })
                        .collect(),
                };
                classes.entry(key.clone()).or_default().push(wi as u32);
                keys.push(key);
            }
            for (wi, k) in keys.iter().enumerate() {
                rel[a][wi] = classes[k].clone();
            }
        }
        let mut m = Model { vals: worlds.into_iter().map(|v| v.into()).collect(), rel, actual: actual as u32 };
        m = contract(&m);
        // memories carried by time-travelling segments
        let mut segs: Vec<(&u32, &Vec<(usize, Value)>)> = self.seg_beliefs.iter().collect();
        segs.sort_by_key(|(a, _)| **a);
        for (a, bel) in segs {
            if bel.is_empty() {
                continue;
            }
            let cs: Vec<Constraint> = bel.iter().map(|(s, v)| Constraint::Slot(*s, v.clone())).collect();
            m = self.private(&m, *a, cs)?;
        }
        Ok(m)
    }

    fn slot_name(&self, s: usize) -> String {
        let sl = &self.world().slots[s];
        if sl.args.is_empty() {
            sl.fact.clone()
        } else {
            format!("{}({})", sl.fact, sl.args.iter().map(|a| self.prog.show(a)).collect::<Vec<_>>().join(", "))
        }
    }

    fn hidden_part(&self, ev: &Ev, env: &Env, e: &E) -> Result<(usize, Option<usize>), String> {
        match &e.kind {
            ExprKind::Field(b, f) => {
                let (s, _) = self.hidden_part(ev, env, b)?;
                let fact = &self.world().facts[&self.world().slots[s].fact];
                match &fact.ty {
                    Ty::Record(_, fs) => {
                        let i = fs.iter().position(|(n, _)| n == f).ok_or(format!("no field '{}'", f))?;
                        Ok((s, Some(i)))
                    }
                    _ => Err(format!("'{}' has no fields", self.prog.text(b.span))),
                }
            }
            _ => Ok((self.target_slot(ev, 0, env, e)?, None)),
        }
    }

    fn target_slot(&self, ev: &Ev, w: u32, env: &Env, e: &E) -> Result<usize, String> {
        match &e.kind {
            ExprKind::Name(n) => ev.slot_index(n, vec![]),
            ExprKind::Call(n, args) => {
                let mut vs = vec![];
                for a in args {
                    vs.push(ev.eval(w, env, a)?);
                }
                ev.slot_index(n, vs)
            }
            _ => Err(format!("'{}' is not a fact", self.prog.text(e.span))),
        }
    }

    /// Who an item in a `seen by` list refers to, at world w.
    fn who(&self, ev: &Ev, w: u32, env: &Env, who: &Who) -> Result<Vec<(u32, Env)>, String> {
        let world = self.world();
        Ok(match who {
            Who::Everyone => world.groups["Agent"].iter().map(|a| (*a, env.clone())).collect(),
            Who::Nobody => vec![],
            Who::Agent(e) => match ev.eval(w, env, e)? {
                Value::Agent(aw, a) if aw as usize == self.wid => vec![(a, env.clone())],
                Value::Unknown => vec![],
                v => return Err(format!("'{}' is {}, not an agent of this world", self.prog.text(e.span), self.prog.show(&v))),
            },
            Who::Every { ty, var, cond } => {
                let g = ty.clone().unwrap_or("Agent".into());
                let members = world.groups.get(&g).ok_or(format!("unknown group '{}'", g))?;
                let mut out = vec![];
                for a in members {
                    let env2 = env_with(env, var, Value::Agent(self.wid as u16, *a));
                    let ok = match cond {
                        Some(c) => ev.truth(w, &env2, c)?,
                        None => true,
                    };
                    if ok {
                        out.push((*a, env2));
                    }
                }
                out
            }
        })
    }

    fn action_env(&self, a: &ActionInst) -> Result<Env, String> {
        let info = self.world().actions.get(&*a.name).ok_or(format!("unknown action '{}'", a.name))?;
        Ok(info.params.iter().zip(a.args.iter()).map(|((n, _), v)| (Rc::from(n.as_str()), v.clone())).collect())
    }

    /// Instantiate an action call written in the timeline or a rule.
    pub fn instantiate(&self, m: &Model, w: u32, c: &Call, env: &Env) -> Result<ActionInst, String> {
        let info = self.world().actions.get(&c.name).ok_or(format!("unknown action '{}'", c.name))?;
        if info.params.len() != c.args.len() {
            return Err(format!("{} takes {} argument(s)", c.name, info.params.len()));
        }
        let ev = self.ev(m);
        let mut args = vec![];
        for ((_, ty), e) in info.params.iter().zip(c.args.iter()) {
            let v = if *ty == Ty::Content {
                let is_event = match &e.kind {
                    ExprKind::SeenAs { .. } => true,
                    ExprKind::Name(_) | ExprKind::Qualified(..) => matches!(ev.eval(w, env, e), Ok(Value::Event(_))),
                    _ => false,
                };
                if is_event {
                    ev.eval(w, env, e)?
                } else {
                    Value::Formula(Rc::new(FormulaVal { expr: e.clone(), env: env.clone(), world: self.wid }))
                }
            } else {
                coerce(self.world(), ty, ev.eval(w, env, e)?)
            };
            args.push(v);
        }
        Ok(ActionInst { name: Rc::from(c.name.as_str()), args })
    }

    // ------------------------------------------------------------ views

    fn observer_views(&self, m: &Model, s: &EvScen, w: u32) -> Result<Vec<Option<Vec<View>>>, String> {
        let na = self.n_agents();
        let world = self.world();
        let ev = self.ev(m);
        let mut out: Vec<Option<Vec<View>>> = vec![None; na];
        match s.step {
            Some(t) => {
                let st = &world.steps[t];
                let items = st.seen_by.as_ref().unwrap();
                for it in items {
                    for (a, env) in self.who(&ev, w, &st.env, &it.who)? {
                        let secret = it.mods.iter().any(|m| matches!(m, Modifier::Secretly));
                        let mut views = vec![View::Full { secret }];
                        for md in &it.mods {
                            match md {
                                Modifier::As(calls) => {
                                    let mut acts = vec![];
                                    for c in calls {
                                        acts.push(self.instantiate(m, w, c, &env)?);
                                    }
                                    views = vec![View::Acts { acts, step_clauses: false, secret }];
                                }
                                Modifier::Hiding(e) => {
                                    let p = match &e.kind {
                                        ExprKind::Name(p) => p.clone(),
                                        _ => return Err("after `hiding` in an event, name one of the action's parameters".into()),
                                    };
                                    let expanded = self.expand_hidden(&s.actions, &[p])?;
                                    views = expanded.into_iter().map(|acts| View::Acts { acts, step_clauses: true, secret }).collect();
                                }
                                Modifier::Secretly => {}
                            }
                        }
                        out[a as usize] = Some(views);
                    }
                }
            }
            None => {
                // per action defaults
                let mut seen: Vec<Vec<(usize, Vec<String>, bool)>> = vec![vec![]; na];
                for (k, act) in s.actions.iter().enumerate() {
                    let info = world.actions.get(&*act.name).ok_or(format!("unknown action '{}'", act.name))?;
                    let env = self.action_env(act)?;
                    if let Some(items) = &info.seen_by {
                        for it in items {
                            for (a, _) in self.who(&ev, w, &env, &it.who)? {
                                let secret = it.mods.iter().any(|m| matches!(m, Modifier::Secretly));
                                let hidden: Vec<String> = it
                                    .mods
                                    .iter()
                                    .filter_map(|m| match m {
                                        Modifier::Hiding(e) => match &e.kind {
                                            ExprKind::Name(p) => Some(p.clone()),
                                            _ => None,
                                        },
                                        _ => None,
                                    })
                                    .collect();
                                seen[a as usize].retain(|(kk, _, _)| *kk != k);
                                seen[a as usize].push((k, hidden, secret));
                            }
                        }
                    }
                }
                for a in 0..na {
                    if seen[a].is_empty() {
                        continue;
                    }
                    let secret = seen[a].iter().any(|x| x.2);
                    let full = seen[a].len() == s.actions.len() && seen[a].iter().all(|x| x.1.is_empty());
                    if full {
                        out[a] = Some(vec![View::Full { secret }]);
                    } else {
                        let mut ks: Vec<&(usize, Vec<String>, bool)> = seen[a].iter().collect();
                        ks.sort_by_key(|x| x.0);
                        let acts: Vec<ActionInst> = ks.iter().map(|x| s.actions[x.0].clone()).collect();
                        let hidden: Vec<String> = ks.iter().flat_map(|x| x.1.clone()).collect();
                        let expanded = self.expand_hidden(&acts, &hidden)?;
                        out[a] = Some(expanded.into_iter().map(|acts| View::Acts { acts, step_clauses: false, secret }).collect());
                    }
                }
            }
        }
        if s.filtered {
            for (a, o) in out.iter_mut().enumerate() {
                let secret = matches!(o.as_ref().and_then(|v| v.first()), Some(View::Full { secret: true }) | Some(View::Acts { secret: true, .. }));
                if secret && s.keep_secret != Some(a as u32) {
                    *o = None;
                }
            }
        }
        Ok(out)
    }

    /// Replace hidden parameters by each possible value (small finite types) or by Unknown.
    fn expand_hidden(&self, acts: &[ActionInst], hidden: &[String]) -> Result<Vec<Vec<ActionInst>>, String> {
        let world = self.world();
        let mut out: Vec<Vec<ActionInst>> = vec![acts.to_vec()];
        for (k, act) in acts.iter().enumerate() {
            let info = &world.actions[&*act.name];
            for (pi, (pn, pt)) in info.params.iter().enumerate() {
                if !hidden.contains(pn) {
                    continue;
                }
                let dom = domain_of(world, pt).filter(|d| d.len() <= 64);
                let mut next = vec![];
                for o in &out {
                    match &dom {
                        Some(d) => {
                            for v in d {
                                let mut o2 = o.clone();
                                o2[k].args[pi] = v.clone();
                                next.push(o2);
                            }
                        }
                        None => {
                            let mut o2 = o.clone();
                            o2[k].args[pi] = Value::Unknown;
                            next.push(o2);
                        }
                    }
                }
                out = next;
            }
        }
        Ok(out)
    }

    fn map_segments(&self, acts: &[ActionInst], perceiver: u32) -> Vec<ActionInst> {
        let world = self.world();
        let pp = world.agents[perceiver as usize].person.unwrap_or(perceiver);
        acts.iter()
            .map(|a| ActionInst {
                name: a.name.clone(),
                args: a
                    .args
                    .iter()
                    .map(|v| match v {
                        Value::Agent(aw, x) if *aw as usize == self.wid => match world.agents[*x as usize].person {
                            Some(base) if base != pp && *x != perceiver => Value::Agent(*aw, base),
                            Some(base) if base == pp || *x == perceiver => v.clone(),
                            _ => v.clone(),
                        },
                        _ => v.clone(),
                    })
                    .collect(),
            })
            .collect()
    }

    fn trusts(&self, m: &Model, a: u32, x: &Value, w: u32) -> bool {
        let world = self.world();
        if !world.honest_relevant {
            return true;
        }
        let Some((xw, xa)) = x.as_agent() else { return true };
        if xw as usize != self.wid {
            return true;
        }
        let Some(&slot) = world.slot_of.get(&("honest".to_string(), vec![Value::Agent(xw, xa)])) else { return true };
        let succ = m.succ(a, w);
        if succ.is_empty() {
            return true;
        }
        !succ.iter().all(|v| m.vals[*v as usize][slot] == Value::Bool(false))
    }

    fn testimony(&self, m: &Model, a: u32, acts: &[ActionInst], w: u32) -> Vec<Value> {
        if self.world().agents[a as usize].mode != Mode::Person {
            return vec![];
        }
        let mut out = vec![];
        for act in acts {
            if &*act.name == "tell" && act.args.len() == 3 {
                if let Value::Formula(_) = &act.args[2] {
                    let teller = act.args[0].as_agent();
                    let world = self.world();
                    let same_person = |x: u32| world.agents[x as usize].person.unwrap_or(x) == world.agents[a as usize].person.unwrap_or(a);
                    let own = matches!(teller, Some((tw, x)) if tw as usize == self.wid && (x == a || (same_person(x) && x == a)));
                    if !own && self.trusts(m, a, &act.args[0], w) {
                        out.push(act.args[2].clone());
                    }
                }
            }
        }
        out
    }

    fn perceive_ev(&self, m: &Model, a: u32, s: &EvScen, w: u32) -> Result<Vec<Scen>, String> {
        let views = self.observer_views(m, s, w)?;
        self.perceive_from_views(m, a, s, w, &views)
    }

    fn perceive_from_views(&self, m: &Model, a: u32, s: &EvScen, w: u32, views: &[Option<Vec<View>>]) -> Result<Vec<Scen>, String> {
        let Some(vs) = &views[a as usize] else { return Ok(vec![Scen::Skip]) };
        let mut out = vec![];
        for v in vs {
            let (acts, step, secret) = match v {
                View::Full { secret } => (s.actions.clone(), s.step, *secret),
                View::Acts { acts, step_clauses, secret } => (acts.clone(), if *step_clauses { s.step } else { None }, *secret),
            };
            let acts = self.map_segments(&acts, a);
            let extra_pre = self.testimony(m, a, &acts, w);
            let lenient = self.world().agents[a as usize].mode == Mode::Person;
            out.push(Scen::Ev(Rc::new(EvScen { actions: acts, step, keep_secret: if secret { Some(a) } else { None }, filtered: true, extra_pre, lenient, ignore_needs: s.ignore_needs })));
        }
        Ok(out)
    }

    /// The actions an agent believes happened in the real event (first reading).
    fn actual_view(&self, m: &Model, a: u32, real: &EvScen) -> Result<Option<Vec<ActionInst>>, String> {
        let ps = self.perceive_ev(m, a, real, m.actual)?;
        Ok(match ps.first() {
            Some(Scen::Ev(s)) => Some(s.actions.clone()),
            _ => None,
        })
    }

    // ------------------------------------------------------------ updates

    pub fn private(&self, m: &Model, agent: u32, cs: Vec<Constraint>) -> Result<Model, String> {
        let cs = Rc::new(cs);
        let mut sys = Sys { r: self, views: HashMap::new() };
        let (m2, _) = product(m, Scen::BelReal(agent, cs), &mut sys)?;
        Ok(contract(&m2))
    }

    pub fn apply_event(&self, m: &Model, t: usize, mut diags: Option<&mut Vec<Diag>>) -> Result<EventOut, String> {
        let world = self.world();
        let st = &world.steps[t];
        let mut actions = vec![];
        for c in &st.actions {
            actions.push(self.instantiate(m, m.actual, c, &st.env).map_err(|e| format!("{}: {}", st.label, e))?);
        }
        if let Some(sup) = self.suppress {
            if actions.iter().any(|a| a.args.first() == Some(&Value::Agent(self.wid as u16, sup))) {
                let na = self.n_agents();
                return Ok(EventOut { model: m.clone(), actual: vec![], views: vec![None; na], triggered_errors: vec![] });
            }
        }
        // preconditions in the actual world
        let mut broken = false;
        {
            let ev = self.ev(m);
            for act in &actions {
                let info = &world.actions[&*act.name];
                let env = self.action_env(act)?;
                for n in &info.needs {
                    match ev.strict_truth(m.actual, &env, n) {
                        Ok(Some(false)) => { broken = true; if let Some(d) = diags.as_deref_mut() { d.push(Diag {
                            level: Level::Error,
                            line: st.span.line,
                            world: world.name.clone(),
                            at: Some(st.label.clone()),
                            msg: format!("{} needs `{}`, which is false here", self.prog.show_action(act), self.prog.text(n.span)),
                        }) } }
                        Err(e) => return Err(format!("{}: {}", st.label, e)),
                        _ => {}
                    }
                }
            }
        }
        let real = Rc::new(EvScen { actions: actions.clone(), step: if st.seen_by.is_some() { Some(t) } else { None }, keep_secret: None, filtered: false, extra_pre: vec![], lenient: false, ignore_needs: broken });
        let na = self.n_agents();
        let mut views = vec![None; na];
        for a in 0..na as u32 {
            views[a as usize] = self.actual_view(m, a, &real)?;
        }
        let mut sys = Sys { r: self, views: HashMap::new() };
        let (m2, nodes) = product(m, Scen::Ev(real), &mut sys).map_err(|e| format!("{}: {}", st.label, e))?;
        let mut actual = actions;
        let mut triggered_errors = vec![];
        let m3 = match self.rule_phase(&m2, &nodes)? {
            Some((m3, trig)) => {
                // needs of triggered actions
                let ev = self.ev(&m2);
                for act in &trig {
                    let info = &world.actions[&*act.name];
                    let env = self.action_env(act)?;
                    for n in &info.needs {
                        if let Ok(Some(false)) = ev.strict_truth(m2.actual, &env, n) {
                            triggered_errors.push(format!("{} needs `{}`, which is false here", self.prog.show_action(act), self.prog.text(n.span)));
                        }
                    }
                }
                // what each agent saw of the triggered actions
                for act in &trig {
                    let info = &world.actions[&*act.name];
                    let env = self.action_env(act)?;
                    if let Some(items) = &info.seen_by {
                        for it in items {
                            for (a, _) in self.who(&ev, m2.actual, &env, &it.who)? {
                                views[a as usize].get_or_insert_with(Vec::new).push(act.clone());
                            }
                        }
                    }
                }
                actual.extend(trig);
                m3
            }
            None => m2,
        };
        Ok(EventOut { model: contract(&m3), actual, views, triggered_errors })
    }

    /// Rules fire in every world; their actions become part of the event.
    fn rule_phase(&self, m: &Model, nodes: &[(u32, Scen)]) -> Result<Option<(Model, Vec<ActionInst>)>, String> {
        let world = self.world();
        let do_rules: Vec<&RuleInfo> = world.rules.iter().filter(|r| matches!((&r.trigger, &r.then), (Trigger::After(_), RuleThen::Do(_)))).collect();
        if do_rules.is_empty() {
            return Ok(None);
        }
        let ev = self.ev(m);
        let mut trig: Vec<Vec<ActionInst>> = vec![vec![]; m.n()];
        for (v, (_, s)) in nodes.iter().enumerate() {
            let Scen::Ev(es) = s else { continue };
            for r in &do_rules {
                let (Trigger::After(pat), RuleThen::Do(call)) = (&r.trigger, &r.then) else { continue };
                for act in &es.actions {
                    let Some(env) = self.match_pattern(&ev, v as u32, pat, act)? else { continue };
                    let envs: Vec<Env> = match &r.for_every {
                        Some((g, var)) => world
                            .groups
                            .get(g)
                            .ok_or(format!("unknown group '{}'", g))?
                            .iter()
                            .map(|a| env_with(&env, var, Value::Agent(self.wid as u16, *a)))
                            .collect(),
                        None => vec![env],
                    };
                    for e2 in envs {
                        let ok = match &r.when {
                            Some(c) => ev.truth(v as u32, &e2, c).map_err(|e| format!("rule {}: {}", r.name, e))?,
                            None => true,
                        };
                        if ok {
                            trig[v].push(self.instantiate(m, v as u32, call, &e2)?);
                        }
                    }
                }
            }
            trig[v].sort_by_key(|a| format!("{:?}", a));
            trig[v].dedup();
        }
        if trig.iter().all(|t| t.is_empty()) {
            return Ok(None);
        }
        // apply effects and refine relations by what each agent observes
        let na = self.n_agents();
        let mut vals = Vec::with_capacity(m.n());
        let mut obs: Vec<Vec<Vec<ActionInst>>> = vec![vec![]; m.n()];
        for v in 0..m.n() {
            let mut cur: Vec<Value> = m.vals[v].to_vec();
            for act in &trig[v] {
                self.apply_effects(m, v as u32, act, &mut cur)?;
            }
            vals.push(cur.into());
            let mut per = vec![vec![]; na];
            for act in &trig[v] {
                let info = &world.actions[&*act.name];
                let env = self.action_env(act)?;
                if let Some(items) = &info.seen_by {
                    for it in items {
                        for (a, _) in self.who(&ev, v as u32, &env, &it.who)? {
                            per[a as usize].push(act.clone());
                        }
                    }
                }
            }
            obs[v] = per;
        }
        let mut rel = vec![vec![Vec::new(); m.n()]; na];
        for a in 0..na {
            for v in 0..m.n() {
                rel[a][v] = m.rel[a][v].iter().copied().filter(|u| obs[*u as usize][a] == obs[v][a]).collect();
            }
        }
        let actual_trig = trig[m.actual as usize].clone();
        Ok(Some((Model { vals, rel, actual: m.actual }, actual_trig)))
    }

    fn match_pattern(&self, ev: &Ev, w: u32, pat: &Call, act: &ActionInst) -> Result<Option<Env>, String> {
        if pat.name != *act.name || pat.args.len() != act.args.len() {
            return Ok(None);
        }
        let world = self.world();
        let mut env: Env = vec![];
        for (p, v) in pat.args.iter().zip(act.args.iter()) {
            if let ExprKind::Name(n) = &p.kind {
                let bound = world.facts.contains_key(n) || world.agent_names.contains_key(n) || world.consts.contains_key(n) || self.prog.params.contains_key(n);
                if !bound {
                    if let Some(prev) = env_get(&env, n) {
                        if prev != v {
                            return Ok(None);
                        }
                    } else {
                        env.push((Rc::from(n.as_str()), v.clone()));
                    }
                    continue;
                }
            }
            if ev.eval(w, &env, p)? != *v {
                return Ok(None);
            }
        }
        Ok(Some(env))
    }

    fn apply_effects(&self, m: &Model, w: u32, act: &ActionInst, cur: &mut [Value]) -> Result<(), String> {
        let world = self.world();
        let info = &world.actions[&*act.name];
        let env = self.action_env(act)?;
        for eff in &info.effects {
            let snapshot: Vec<Value> = cur.to_vec();
            let ev = Ev { vals: Some(&snapshot), ..self.ev(m) };
            let slot = match self.target_slot(&ev, w, &env, &eff.target) {
                Ok(s) => s,
                Err(_) if act.args.contains(&Value::Unknown) => continue,
                Err(e) => return Err(e),
            };
            let v = ev.eval(w, &env, &eff.value)?;
            if v == Value::Unknown {
                continue;
            }
            cur[slot] = coerce(world, &world.facts[&world.slots[slot].fact].ty, v);
        }
        Ok(())
    }

    // ------------------------------------------------------------ conclusions

    fn pending_conclusions(&self, m: &Model, t: usize, views: &[Option<Vec<ActionInst>>], actual: &[ActionInst]) -> Result<Vec<PendingConcl>, String> {
        let world = self.world();
        let st = &world.steps[t];
        let mut out = vec![];
        for (i, c) in st.conclusions.iter().enumerate() {
            out.push(PendingConcl {
                key: (t, format!("a{}", i)),
                agent_expr: Some(c.agent.clone()),
                agent: None,
                formula: c.formula.clone(),
                env: st.env.clone(),
                because: c.because.clone(),
                despite: c.despite.clone(),
                line: c.span.line,
            });
        }
        let ev = self.ev(m);
        for (ri, r) in world.rules.iter().enumerate() {
            let RuleThen::Concludes(agent_e, f) = &r.then else { continue };
            let candidates: Vec<(Option<u32>, Vec<ActionInst>)> = match &r.trigger {
                Trigger::After(_) => vec![(None, actual.to_vec())],
                Trigger::AfterSees(a, _) => {
                    let av = ev.eval(m.actual, &vec![], a)?.as_agent().ok_or("expected an agent")?;
                    vec![(Some(av.1), views[av.1 as usize].clone().unwrap_or_default())]
                }
            };
            let pat = match &r.trigger {
                Trigger::After(p) | Trigger::AfterSees(_, p) => p,
            };
            for (who, acts) in candidates {
                for act in &acts {
                    let Some(env) = self.match_pattern(&ev, m.actual, pat, act)? else { continue };
                    let ok = match &r.when {
                        Some(c) => ev.truth(m.actual, &env, c)?,
                        None => true,
                    };
                    if ok {
                        out.push(PendingConcl {
                            key: (t, format!("r{}:{:?}", ri, env)),
                            agent_expr: if who.is_some() { None } else { Some(agent_e.clone()) },
                            agent: who,
                            formula: f.clone(),
                            env: env.clone(),
                            because: None,
                            despite: None,
                            line: r.span.line,
                        });
                    }
                }
            }
        }
        Ok(out)
    }

    fn concl_agent(&self, m: &Model, p: &PendingConcl) -> Result<u32, String> {
        if let Some(a) = p.agent {
            return Ok(a);
        }
        let e = p.agent_expr.as_ref().unwrap();
        match self.ev(m).eval(m.actual, &p.env, e)? {
            Value::Agent(aw, a) if aw as usize == self.wid => Ok(a),
            _ => Err(format!("'{}' is not an agent of this world", self.prog.text(e.span))),
        }
    }

    /// Replay from the start, applying all conclusions except the disabled ones.
    pub fn simulate(&self, upto: usize, disabled: &HashSet<CKey>, include_last: bool) -> Result<Model, String> {
        let mut m = self.initial()?;
        for t in 0..=upto {
            let (views, actual) = if t > 0 {
                let out = self.apply_event(&m, t, None)?;
                m = out.model;
                (out.views, out.actual)
            } else {
                (vec![None; self.n_agents()], vec![])
            };
            if t == upto && !include_last {
                break;
            }
            for p in self.pending_conclusions(&m, t, &views, &actual)? {
                if disabled.contains(&p.key) {
                    continue;
                }
                let ev = self.ev(&m);
                if ev.foreign_world(&p.formula)?.is_some() {
                    continue;
                }
                let a = self.concl_agent(&m, &p)?;
                let f = Value::Formula(Rc::new(FormulaVal { expr: p.formula.clone(), env: p.env.clone(), world: self.wid }));
                m = self.private(&m, a, vec![Constraint::F(f)])?;
            }
        }
        Ok(m)
    }

    // ------------------------------------------------------------ main pass

    pub fn run(&self) -> Run {
        let world = self.world();
        let mut diags: Vec<Diag> = vec![];
        let mut snaps: Vec<Snap> = vec![];
        let na = self.n_agents();
        let mut all_concl: Vec<ConclRec> = vec![];
        let diag = |diags: &mut Vec<Diag>, level: Level, line: usize, t: usize, msg: String| {
            diags.push(Diag { level, line, world: world.name.clone(), at: Some(world.steps[t].label.clone()), msg });
        };
        let mut model = match self.initial() {
            Ok(m) => m,
            Err(e) => {
                diags.push(Diag { level: Level::Error, line: world.steps[0].span.line, world: world.name.clone(), at: Some("start".into()), msg: e });
                return Run { world: self.wid, snaps, diags, conclusions: all_concl, seg_beliefs: self.seg_beliefs.clone() };
            }
        };
        let mut reg = Registry::new(na);
        let mut foreign_map: ForeignMap = ForeignMap::new();
        let mut disabled: HashSet<CKey> = HashSet::new();
        let mut active: Vec<ConclRec> = vec![];
        let mut reported_empty_global: HashSet<u32> = HashSet::new();

        for t in 0..world.steps.len() {
            let st = &world.steps[t];
            let mut views = vec![None; na];
            let mut actual = vec![];
            if t > 0 {
                // because on the event itself, checked just before it
                if let Some(b) = &st.because {
                    let ev = Ev { registry: Some(&reg), foreign: Some(&foreign_map), ..self.ev(&model) };
                    match ev.strict_truth(model.actual, &st.env, b) {
                        Ok(Some(false)) => diag(&mut diags, Level::Error, st.span.line, t, format!("this happens because `{}`, but that isn't true just before {}", self.prog.text(b.span), st.label)),
                        Err(e) => diag(&mut diags, Level::Error, st.span.line, t, e),
                        _ => {}
                    }
                }
                // telling about an event needs a view of it
                for c in &st.actions {
                    if c.name != "tell" {
                        continue;
                    }
                    if let Ok(act) = self.instantiate(&model, model.actual, c, &st.env) {
                        if let (Some(Value::Agent(xw, x)), Some(Value::Event(r))) = (act.args.first(), act.args.get(2)) {
                            if self.resolve_view(&reg, &foreign_map, (*xw, *x), r, None, &snaps).is_none() {
                                diag(&mut diags, Level::Error, st.span.line, t, format!("{} tells about {}, but never saw or heard of it", self.prog.agent_name(*xw, *x), self.prog.show(&act.args[2])));
                            }
                        }
                    }
                }
                let pre_model = model.clone();
                let errors_before = diags.iter().filter(|d| d.level == Level::Error).count();
                match self.apply_event(&model, t, Some(&mut diags)) {
                    Ok(out) => {
                        for e in &out.triggered_errors {
                            diag(&mut diags, Level::Error, st.span.line, t, e.clone());
                        }
                        model = out.model;
                        views = out.views;
                        actual = out.actual;
                    }
                    Err(e) => {
                        diag(&mut diags, Level::Error, st.span.line, t, e);
                        return self.abort(snaps, diags, all_concl);
                    }
                }
                if diags.iter().filter(|d| d.level == Level::Error).count() > errors_before {
                    // the event itself is broken; don't pile on with consequences
                    for a in 0..na as u32 {
                        reported_empty_global.insert(a);
                    }
                }
                for a in 0..na {
                    if let Some(v) = &views[a] {
                        reg.views[a].insert(st.label.clone(), ViewRec { actions: v.clone(), direct: true, step: t, actual: actual.clone() });
                    }
                }
                // second-hand views: tells whose content is an event
                for a in 0..na {
                    if world.agents[a].mode != Mode::Person {
                        continue;
                    }
                    let Some(v) = views[a].clone() else { continue };
                    for act in &v {
                        if &*act.name != "tell" || act.args.len() != 3 {
                            continue;
                        }
                        let (Some((xw, x)), Value::Event(r)) = (act.args[0].as_agent(), &act.args[2]) else { continue };
                        if !self.trusts(&pre_model, a as u32, &act.args[0], pre_model.actual) {
                            continue;
                        }
                        let Some(acts) = self.resolve_view(&reg, &foreign_map, (xw, x), r, None, &snaps) else { continue };
                        self.adopt(&mut reg, &mut foreign_map, &mut diags, a as u32, r.world, &r.label, acts, t, &snaps, 0);
                    }
                }
            }
            // retractions
            let mut reported_empty: HashSet<u32> = std::mem::take(&mut reported_empty_global);
            loop {
                let mut gone: Vec<(usize, String)> = vec![];
                for (i, c) in active.iter().enumerate() {
                    if let Some(reason) = self.retraction_reason(&model, &reg, &foreign_map, c) {
                        gone.push((i, reason));
                    }
                }
                // an observation that contradicts a conclusion: drop the newest one
                if gone.is_empty() {
                    for a in 0..na as u32 {
                        if !model.succ(a, model.actual).is_empty() || reported_empty.contains(&a) {
                            continue;
                        }
                        if let Some(i) = active.iter().rposition(|c| c.agent == a && c.foreign.is_none()) {
                            gone.push((i, format!("what they saw at {} contradicts it", st.label)));
                            break;
                        }
                        reported_empty.insert(a);
                        diag(&mut diags, Level::Error, st.span.line, t, format!("{}'s beliefs became contradictory: they saw something they thought impossible", world.agents[a as usize].name));
                    }
                }
                if gone.is_empty() {
                    break;
                }
                for (i, reason) in gone.iter().rev() {
                    let c = active.remove(*i);
                    disabled.insert(c.key.clone());
                    diag(&mut diags, Level::Note, c.line, t, format!("{} no longer believes `{}`: {}", world.agents[c.agent as usize].name, self.prog.show(&c.formula), reason));
                }
                match self.simulate(t, &disabled, false) {
                    Ok(m) => model = m,
                    Err(e) => {
                        diag(&mut diags, Level::Error, st.span.line, t, e);
                        return self.abort(snaps, diags, all_concl);
                    }
                }
            }
            // foreign retractions
            let keys: Vec<(u32, usize)> = foreign_map.keys().copied().collect();
            for k in keys {
                loop {
                    let st_f = foreign_map[&k].clone();
                    let mut gone = None;
                    for (i, c) in st_f.active.iter().enumerate() {
                        if let Some(reason) = self.retraction_reason(&model, &reg, &foreign_map, c) {
                            gone = Some((i, reason));
                            break;
                        }
                    }
                    let Some((i, reason)) = gone else { break };
                    let c = foreign_map.get_mut(&k).unwrap().active.remove(i);
                    diag(&mut diags, Level::Note, c.line, t, format!("{} no longer believes `{}`: {}", world.agents[c.agent as usize].name, self.prog.show(&c.formula), reason));
                }
            }
            // new conclusions
            let pending = match self.pending_conclusions(&model, t, &views, &actual) {
                Ok(p) => p,
                Err(e) => {
                    diag(&mut diags, Level::Error, st.span.line, t, e);
                    vec![]
                }
            };
            for p in pending {
                match self.conclude(&mut model, &reg, &mut foreign_map, &mut active, &mut disabled, &mut diags, t, &p) {
                    Ok(Some(rec)) => all_concl.push(rec),
                    Ok(None) => {
                        disabled.insert(p.key.clone());
                    }
                    Err(e) => {
                        disabled.insert(p.key.clone());
                        diag(&mut diags, Level::Error, p.line, t, e);
                    }
                }
            }
            snaps.push(Snap { model: Rc::new(model.clone()), registry: Rc::new(reg.clone()), foreign: Rc::new(foreign_map.clone()), actual, disabled: Rc::new(disabled.clone()) });
        }
        Run { world: self.wid, snaps, diags, conclusions: all_concl, seg_beliefs: self.seg_beliefs.clone() }
    }

    fn abort(&self, snaps: Vec<Snap>, mut diags: Vec<Diag>, concl: Vec<ConclRec>) -> Run {
        let world = self.world();
        diags.push(Diag { level: Level::Note, line: 0, world: world.name.clone(), at: None, msg: "checking of this world stopped here".into() });
        Run { world: self.wid, snaps, diags, conclusions: concl, seg_beliefs: self.seg_beliefs.clone() }
    }

    /// The view a teller would pass on.
    fn resolve_view(&self, reg: &Registry, fm: &ForeignMap, teller: (u16, u32), r: &EventRef, at_step: Option<usize>, snaps: &[Snap]) -> Option<Vec<ActionInst>> {
        let prog = self.prog;
        let ew = &prog.worlds[r.world];
        let estep = *ew.label_index.get(&r.label)?;
        let reg_at = |world: usize, step: usize| -> Option<Rc<Registry>> {
            if world == self.wid {
                snaps.get(step).map(|s| s.registry.clone())
            } else {
                self.hub.snap(world, step).map(|s| s.registry.clone())
            }
        };
        if let Some((sw, s)) = r.seen_by {
            let g = reg_at(sw as usize, estep)?;
            return g.views.get(s as usize)?.get(&r.label).map(|v| v.actions.clone());
        }
        let (tw, x) = (teller.0 as usize, teller.1);
        if tw == self.wid {
            if r.world == self.wid {
                return reg.views[x as usize].get(&r.label).map(|v| v.actions.clone());
            }
            if prog.worlds[tw].agents[x as usize].sees_all_of == Some(r.world) {
                return self.hub.snap(r.world, estep).map(|s| s.actual.clone());
            }
            return fm.get(&(x, r.world)).and_then(|f| f.views.get(&r.label)).map(|v| v.0.clone());
        }
        // a teller inside another world, at the time they told it
        let step = at_step?;
        let g = reg_at(tw, step)?;
        g.views.get(x as usize)?.get(&r.label).map(|v| v.actions.clone())
    }

    #[allow(clippy::too_many_arguments)]
    fn adopt(&self, reg: &mut Registry, fm: &mut ForeignMap, diags: &mut Vec<Diag>, a: u32, ew: usize, label: &str, acts: Vec<ActionInst>, t: usize, snaps: &[Snap], depth: usize) {
        let world = self.world();
        let st = &world.steps[t];
        let estep = match self.prog.worlds[ew].label_index.get(label) {
            Some(s) => *s,
            None => return,
        };
        let old: Option<Vec<ActionInst>> = if ew == self.wid {
            reg.views[a as usize].get(label).map(|v| v.actions.clone())
        } else {
            fm.get(&(a, ew)).and_then(|f| f.views.get(label)).map(|v| v.0.clone())
        };
        if let Some(old) = &old {
            if !contains(&acts, old) {
                diags.push(Diag {
                    level: Level::Error,
                    line: st.span.line,
                    world: world.name.clone(),
                    at: Some(st.label.clone()),
                    msg: format!(
                        "{} is told {} was `{}`, which contradicts what they believed (`{}`); resolve it with a conclusion",
                        world.agents[a as usize].name,
                        label,
                        self.prog.show_actions(&acts),
                        self.prog.show_actions(old)
                    ),
                });
                return;
            }
        }
        if ew == self.wid {
            let actual = snaps.get(estep).map(|s| s.actual.clone()).unwrap_or_default();
            reg.views[a as usize].insert(label.to_string(), ViewRec { actions: acts.clone(), direct: false, step: estep, actual });
        } else {
            fm.entry((a, ew)).or_default().views.insert(label.to_string(), (acts.clone(), estep));
        }
        if depth > 4 {
            return;
        }
        // nested tellings inside the adopted view
        for act in &acts {
            if &*act.name != "tell" || act.args.len() != 3 {
                continue;
            }
            let (Some(teller), Value::Event(r)) = (act.args[0].as_agent(), &act.args[2]) else { continue };
            let inner = self.resolve_view(reg, fm, teller, r, Some(estep), snaps);
            if let Some(inner) = inner {
                self.adopt(reg, fm, diags, a, r.world, &r.label, inner, t, snaps, depth + 1);
            }
        }
    }

    fn retraction_reason(&self, m: &Model, reg: &Registry, fm: &ForeignMap, c: &ConclRec) -> Option<String> {
        for (i, (ew, label)) in c.event_sources.iter().enumerate() {
            if c.despite.contains(&(*ew, label.clone())) {
                continue;
            }
            let now: Option<Vec<ActionInst>> = if *ew == self.wid {
                reg.views[c.agent as usize].get(label).map(|v| v.actions.clone())
            } else {
                fm.get(&(c.agent, *ew)).and_then(|f| f.views.get(label)).map(|v| v.0.clone())
            };
            if now != c.snapshot[i] {
                let shown = now.map(|n| self.prog.show_actions(&n)).unwrap_or("nothing".into());
                return Some(format!("{} now looks like `{}`", label, shown));
            }
        }
        for b in &c.belief_sources {
            let Value::Formula(f) = b else { continue };
            let held = match c.foreign {
                Some(tw) => foreign::believes(self.prog, tw, &fm.get(&(c.agent, tw)).cloned().unwrap_or_default(), &f.env, &f.expr),
                None => {
                    let ev = self.ev(m);
                    match ev.foreign_world(&f.expr) {
                        Ok(Some(tw)) => foreign::believes(self.prog, tw, &fm.get(&(c.agent, tw)).cloned().unwrap_or_default(), &f.env, &f.expr),
                        _ => ev.kripke_epistemic(m.actual, c.agent, KMode::Believes, &f.env, &f.expr).unwrap_or(true),
                    }
                }
            };
            if !held {
                return Some(format!("it rested on `{}`, which they no longer believe", self.prog.text(f.expr.span)));
            }
        }
        None
    }

    #[allow(clippy::too_many_arguments)]
    fn conclude(
        &self,
        model: &mut Model,
        reg: &Registry,
        fm: &mut ForeignMap,
        active: &mut Vec<ConclRec>,
        disabled: &mut HashSet<CKey>,
        diags: &mut Vec<Diag>,
        t: usize,
        p: &PendingConcl,
    ) -> Result<Option<ConclRec>, String> {
        let world = self.world();
        let a = self.concl_agent(model, p)?;
        let aname = world.agents[a as usize].name.clone();
        let fval = Value::Formula(Rc::new(FormulaVal { expr: p.formula.clone(), env: p.env.clone(), world: self.wid }));
        let ev = self.ev(model);
        let tw = ev.foreign_world(&p.formula)?;
        // split sources into events and beliefs
        let mut parts = vec![];
        if let Some(b) = &p.because {
            split_and(b, &mut parts);
        }
        let mut event_sources = vec![];
        let mut belief_sources = vec![];
        for part in parts {
            match ev.eval(model.actual, &p.env, &part) {
                Ok(Value::Event(r)) => event_sources.push((r.world, r.label.clone())),
                _ => belief_sources.push(Value::Formula(Rc::new(FormulaVal { expr: part.clone(), env: p.env.clone(), world: self.wid }))),
            }
        }
        let mut despite = vec![];
        if let Some(d) = &p.despite {
            let mut ds = vec![];
            split_and(d, &mut ds);
            for part in ds {
                match ev.eval(model.actual, &p.env, &part) {
                    Ok(Value::Event(r)) => despite.push((r.world, r.label.clone())),
                    _ => return Err(format!("after `despite`, name an event (got `{}`)", self.prog.text(part.span))),
                }
            }
        }
        // check sources
        let view_of = |fm: &ForeignMap, ew: usize, label: &str| -> Option<Vec<ActionInst>> {
            if ew == self.wid {
                reg.views[a as usize].get(label).map(|v| v.actions.clone())
            } else {
                fm.get(&(a, ew)).and_then(|f| f.views.get(label)).map(|v| v.0.clone())
            }
        };
        let mut snapshot = vec![];
        for (ew, label) in event_sources.iter().chain(despite.iter()) {
            let v = view_of(fm, *ew, label);
            if v.is_none() {
                return Err(format!("{} concludes `{}` because of {}, but never saw or heard of {}", aname, self.prog.text(p.formula.span), label, label));
            }
        }
        for (ew, label) in &event_sources {
            snapshot.push(view_of(fm, *ew, label));
        }
        for b in &belief_sources {
            let Value::Formula(f) = b else { continue };
            let held = match ev.foreign_world(&f.expr)? {
                Some(fw) => foreign::believes(self.prog, fw, &fm.get(&(a, fw)).cloned().unwrap_or_default(), &f.env, &f.expr),
                None => ev.kripke_epistemic(model.actual, a, KMode::Believes, &f.env, &f.expr)?,
            };
            if !held {
                return Err(format!("{} concludes `{}` because `{}`, but doesn't believe that", aname, self.prog.text(p.formula.span), self.prog.text(f.expr.span)));
            }
        }
        let rec = ConclRec {
            key: p.key.clone(),
            agent: a,
            formula: fval.clone(),
            event_sources,
            belief_sources,
            despite,
            step: t,
            snapshot,
            foreign: tw,
            line: p.line,
        };
        if let Some(tw) = tw {
            let st = fm.entry((a, tw)).or_default();
            if foreign::believes_not(self.prog, tw, st, &p.env, &p.formula) {
                // revise: drop own conclusions that contradict
                let before = st.active.len();
                let mut kept = vec![];
                for c in st.active.drain(..) {
                    kept.push(c);
                }
                let mut trial = ForeignStore { views: st.views.clone(), active: vec![] };
                for c in kept {
                    trial.active.push(c.clone());
                    if foreign::believes_not(self.prog, tw, &trial, &p.env, &p.formula) {
                        trial.active.pop();
                        diags.push(Diag { level: Level::Note, line: p.line, world: world.name.clone(), at: Some(world.steps[t].label.clone()), msg: format!("{} revises: drops `{}`", aname, self.prog.show(&c.formula)) });
                    }
                }
                st.active = trial.active;
                let _ = before;
                if foreign::believes_not(self.prog, tw, st, &p.env, &p.formula) {
                    return Err(format!("{} concludes `{}`, but what they were told rules it out", aname, self.prog.text(p.formula.span)));
                }
            }
            st.active.push(rec.clone());
            return Ok(Some(rec));
        }
        // consistency with current beliefs; revise own conclusions if needed
        let consistent = |m: &Model| -> Result<bool, String> {
            let ev = self.ev(m);
            for &v in m.succ(a, m.actual) {
                if ev.truth(v, &p.env, &p.formula)? {
                    return Ok(true);
                }
            }
            Ok(false)
        };
        if !consistent(model)? {
            let own: Vec<usize> = active.iter().enumerate().filter(|(_, c)| c.agent == a).map(|(i, _)| i).rev().collect();
            let mut dropped = vec![];
            let mut ok = false;
            for i in own {
                dropped.push(i);
                let mut dis = disabled.clone();
                for &j in &dropped {
                    dis.insert(active[j].key.clone());
                }
                let mut m = self.simulate(t, &dis, false)?;
                for c in active.iter().filter(|c| c.step == t && !dis.contains(&c.key) && c.foreign.is_none()) {
                    m = self.private(&m, c.agent, vec![Constraint::F(c.formula.clone())])?;
                }
                if consistent(&m)? {
                    *model = m;
                    ok = true;
                    break;
                }
            }
            if !ok {
                return Err(format!("{} concludes `{}`, but what they have seen rules it out", aname, self.prog.text(p.formula.span)));
            }
            dropped.sort_unstable();
            for i in dropped.into_iter().rev() {
                let c = active.remove(i);
                disabled.insert(c.key.clone());
                diags.push(Diag { level: Level::Note, line: p.line, world: world.name.clone(), at: Some(world.steps[t].label.clone()), msg: format!("{} revises: drops `{}`", aname, self.prog.show(&c.formula)) });
            }
        }
        *model = self.private(model, a, vec![Constraint::F(fval)])?;
        active.push(rec.clone());
        Ok(Some(rec))
    }
}

pub fn split_and(e: &E, out: &mut Vec<E>) {
    if let ExprKind::Bin(BinOp::And, a, b) = &e.kind {
        split_and(a, out);
        split_and(b, out);
    } else {
        out.push(e.clone());
    }
}

/// Does view `new` include everything in `old`? (Seeing more of the same event.)
pub fn contains(new: &[ActionInst], old: &[ActionInst]) -> bool {
    old.iter().all(|o| {
        new.iter().any(|n| n.name == o.name && n.args.len() == o.args.len() && n.args.iter().zip(o.args.iter()).all(|(x, y)| x == y || *x == Value::Unknown || *y == Value::Unknown))
    })
}

struct Sys<'r, 'a> {
    r: &'r Runner<'a>,
    /// Observer views depend only on (scenario, world); compute them once.
    views: HashMap<(Rc<EvScen>, u32), Rc<Vec<Option<Vec<View>>>>>,
}

impl<'r, 'a> Scenarios for Sys<'r, 'a> {
    type S = Scen;

    fn perceive(&mut self, m: &Model, agent: u32, s: &Scen, w: u32) -> Result<Vec<Scen>, String> {
        Ok(match s {
            Scen::Skip => vec![Scen::Skip],
            Scen::BelReal(x, cs) | Scen::BelImg(x, cs) => {
                if *x == agent {
                    vec![Scen::BelImg(*x, cs.clone())]
                } else {
                    vec![Scen::Skip]
                }
            }
            Scen::Ev(es) => {
                let key = (es.clone(), w);
                let views = match self.views.get(&key) {
                    Some(v) => v.clone(),
                    None => {
                        let v = Rc::new(self.r.observer_views(m, es, w)?);
                        self.views.insert(key, v.clone());
                        v
                    }
                };
                self.r.perceive_from_views(m, agent, es, w, &views)?
            }
        })
    }

    fn pre(&mut self, m: &Model, s: &Scen, w: u32) -> Result<bool, String> {
        let ev = self.r.ev(m);
        match s {
            Scen::Skip | Scen::BelReal(..) => Ok(true),
            Scen::BelImg(_, cs) => {
                for c in cs.iter() {
                    let ok = match c {
                        Constraint::Slot(slot, v) => m.vals[w as usize][*slot] == *v,
                        Constraint::F(Value::Formula(f)) => ev.truth(w, &f.env, &f.expr)?,
                        Constraint::F(_) => true,
                    };
                    if !ok {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Scen::Ev(es) => {
                let world = self.r.world();
                for act in &es.actions {
                    if es.ignore_needs || (es.lenient && &*act.name == "tell") {
                        continue;
                    }
                    let info = world.actions.get(&*act.name).ok_or(format!("unknown action '{}'", act.name))?;
                    let env = self.r.action_env(act)?;
                    for n in &info.needs {
                        if !ev.truth(w, &env, n)? {
                            return Ok(false);
                        }
                    }
                }
                for f in &es.extra_pre {
                    if let Value::Formula(f) = f {
                        if !ev.truth(w, &f.env, &f.expr)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
        }
    }

    fn post(&mut self, m: &Model, s: &Scen, w: u32) -> Result<Rc<[Value]>, String> {
        match s {
            Scen::Ev(es) => {
                let mut cur: Vec<Value> = m.vals[w as usize].to_vec();
                for act in &es.actions {
                    self.r.apply_effects(m, w, act, &mut cur)?;
                }
                Ok(cur.into())
            }
            _ => Ok(m.vals[w as usize].clone()),
        }
    }
}
