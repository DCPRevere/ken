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
    /// an imagined change: the slot now has this value
    Set(usize, Value),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Scen {
    Skip,
    /// nothing this agent saw happened at this step (worlds with `may happen unseen`)
    Quiet(usize),
    Ev(Rc<EvScen>),
    BelReal(u32, Rc<Vec<Constraint>>),
    BelImg(u32, Rc<Vec<Constraint>>),
    /// a (first) privately imagines that b (second) has come to believe the constraints
    NestReal(u32, u32, Rc<Vec<Constraint>>),
    NestImg(u32, u32, Rc<Vec<Constraint>>),
    /// the agent forgets a fact: they no longer know its value
    ForgetReal(u32, usize),
    /// in the forgetful agent's imagination, the fact has this value
    SetImg(u32, usize, Value),
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EvScen {
    pub actions: Vec<ActionInst>,
    pub step: Option<usize>,
    /// whose secret views are kept in this scenario (the perceiver's own, and
    /// those whose secret the perceiver is in on)
    pub keep_secret: Vec<u32>,
    /// secret observers who, in this scenario, think nobody knows about them
    pub naive: Vec<u32>,
    pub filtered: bool,
    pub extra_pre: Vec<Value>,
    /// Perceived by a person: trusted testimony is taken at face value,
    /// without reasoning about how the teller knew.
    pub lenient: bool,
    /// The event's preconditions failed in reality (already reported):
    /// observers learn nothing from them.
    pub ignore_needs: bool,
    /// The step this event is.
    pub at: usize,
    /// Perceived by a person who found it impossible: preconditions and testimony
    /// about changeable facts are taken as news of an unseen change, not as filters.
    pub revise: bool,
    /// imagined by a logician who didn't see this step: it happened, out of their sight
    pub unseen_by: Option<u32>,
}

#[derive(Clone, Debug)]
enum View {
    Full {
        secret: bool,
        known_to: Rc<[u32]>,
    },
    Acts {
        acts: Vec<ActionInst>,
        step_clauses: bool,
        secret: bool,
        known_to: Rc<[u32]>,
    },
}

impl View {
    fn secret(&self) -> bool {
        match self {
            View::Full { secret, .. } | View::Acts { secret, .. } => *secret,
        }
    }
    /// For a secret view: the other agents who know about it.
    fn known_to(&self) -> &[u32] {
        match self {
            View::Full { known_to, .. } | View::Acts { known_to, .. } => known_to,
        }
    }
}

pub struct Runner<'a> {
    pub prog: &'a Program,
    pub wid: usize,
    pub hub: &'a dyn Hub,
    pub seg_beliefs: HashMap<u32, Vec<(usize, Value)>>,
    pub suppress: Option<u32>,
    /// (listener, teller): testimony the listener has withdrawn, because they
    /// came to believe the teller dishonest. It applies retroactively.
    pub distrust: std::cell::RefCell<HashSet<(u32, u32)>>,
    /// (person, step): the person assumes unseen changes to make sense of this step.
    pub revise: std::cell::RefCell<HashSet<(u32, usize)>>,
    /// (listener, step): testimony the listener has set aside, because a later
    /// conclusion of theirs contradicts it.
    pub set_aside: std::cell::RefCell<HashSet<(u32, usize)>>,
    /// conclusions about changeable facts taken as "it has changed" rather than a filter
    pub as_change: std::cell::RefCell<HashSet<CKey>>,
    /// (agent, step): for "why" questions, the agent is made not to see that step
    pub blind: std::cell::RefCell<HashSet<(u32, usize)>>,
    /// conclusions left out from the start, for "why" questions
    pub pre_disabled: std::cell::RefCell<HashSet<CKey>>,
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

/// What revision gave up: an own conclusion (index into the active list) or the
/// testimony accepted at a step (step, teller).
#[derive(Clone, Copy, Debug, PartialEq)]
enum Revised {
    Concl(usize),
    Told(usize, u32),
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
    pub fn new(
        prog: &'a Program,
        wid: usize,
        hub: &'a dyn Hub,
        seg_beliefs: HashMap<u32, Vec<(usize, Value)>>,
        suppress: Option<u32>,
    ) -> Self {
        Runner {
            prog,
            wid,
            hub,
            seg_beliefs,
            suppress,
            distrust: Default::default(),
            revise: Default::default(),
            set_aside: Default::default(),
            as_change: Default::default(),
            blind: Default::default(),
            pre_disabled: Default::default(),
        }
    }

    pub fn world(&self) -> &'a World {
        &self.prog.worlds[self.wid]
    }

    fn ev<'b>(&'b self, m: &'b Model) -> Ev<'b> {
        Ev {
            prog: self.prog,
            wid: self.wid,
            model: m,
            step: 0,
            registry: None,
            foreign: None,
            hub: Some(self.hub),
            vals: None,
            depth: Default::default(),
        }
    }

    fn n_agents(&self) -> usize {
        self.world().agents.len()
    }

    // ------------------------------------------------------------ initial model

    /// Truth at start, what each agent observed of it, and which slots vary.
    pub fn initial_state(&self) -> Result<InitState, String> {
        let w = self.world();
        let start = &w.steps[0];
        let blank = Model {
            vals: vec![],
            rel: vec![],
            actual: 0,
        };
        let mut truth: Vec<Option<Value>> = vec![None; w.slots.len()];
        // defaults
        for (ix, s) in w.slots.iter().enumerate() {
            let f = &w.facts[&s.fact];
            if let Some(d) = &f.default {
                let vals: Vec<Value> = vec![Value::Unknown; w.slots.len()];
                let ev = Ev {
                    vals: Some(&vals),
                    ..self.ev(&blank)
                };
                truth[ix] = Some(ev.eval(0, &vec![], d)?);
            }
        }
        // assignments in start
        for a in &start.assigns {
            let mut envs: Vec<Env> = vec![start.env.clone()];
            if let Some((v, lo, hi)) = &a.for_range {
                let lo = const_int(lo, &self.prog.params, &start.env).map_err(|e| e.1)?;
                let hi = const_int(hi, &self.prog.params, &start.env).map_err(|e| e.1)?;
                envs = (lo..=hi)
                    .map(|k| env_with(&start.env, v, Value::Int(k)))
                    .collect();
            }
            for env in envs {
                let vals: Vec<Value> = truth
                    .iter()
                    .map(|t| t.clone().unwrap_or(Value::Unknown))
                    .collect();
                let ev = Ev {
                    vals: Some(&vals),
                    ..self.ev(&blank)
                };
                let slot = self
                    .target_slot(&ev, 0, &env, &a.target)
                    .map_err(|m| format!("line {}: {}", a.span.line, m))?;
                let v = ev
                    .eval(0, &env, &a.value)
                    .map_err(|m| format!("line {}: {}", a.span.line, m))?;
                let v = coerce(w, &w.facts[&w.slots[slot].fact].ty, v);
                if !w.slots[slot].domain.is_empty() && !w.slots[slot].domain.contains(&v) {
                    return Err(format!(
                        "line {}: {} can't be {}",
                        a.span.line,
                        self.slot_name(slot),
                        self.prog.show(&v)
                    ));
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
                    tv.push(
                        w.slots[ix]
                            .domain
                            .first()
                            .cloned()
                            .unwrap_or(Value::Unknown),
                    );
                }
            }
        }
        // observations of the initial state
        let na = self.n_agents();
        // per agent: None = saw nothing; Some(hidden) where hidden = (slot, field)
        let mut obs: Vec<Option<Vec<(usize, Option<usize>)>>> = vec![None; na];
        if let Some(items) = &start.seen_by {
            let tm = Model {
                vals: vec![tv.clone().into()],
                rel: vec![vec![vec![0]]; na],
                actual: 0,
            };
            let ev = self.ev(&tm);
            for it in items {
                let agents = self.who(&ev, 0, &start.env, &it.who)?;
                for (a, env) in agents {
                    let mut hidden = obs[a as usize].take().unwrap_or_default();
                    for m in &it.mods {
                        match m {
                            Modifier::Hiding(e) => hidden.push(self.hidden_part(&ev, &env, e)?),
                            Modifier::Secretly(_) => {}
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
        Ok(InitState {
            truth: tv,
            obs,
            varying,
        })
    }

    pub fn initial(&self) -> Result<Model, String> {
        let w = self.world();
        let na = self.n_agents();
        let InitState {
            truth: tv,
            obs,
            varying,
        } = self.initial_state()?;
        let mut count: usize = 1;
        for &s in &varying {
            count = count.saturating_mul(w.slots[s].domain.len().max(1));
        }
        if count > 500_000 {
            return Err(format!(
                "{} possible starting worlds is too many; reduce what is hidden or the parameters",
                count
            ));
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
        let mut m = Model {
            vals: worlds.into_iter().map(|v| v.into()).collect(),
            rel,
            actual: actual as u32,
        };
        m = contract(&m);
        // memories carried by time-travelling segments
        let mut segs: Vec<(&u32, &Vec<(usize, Value)>)> = self.seg_beliefs.iter().collect();
        segs.sort_by_key(|(a, _)| **a);
        for (a, bel) in segs {
            if bel.is_empty() {
                continue;
            }
            let cs: Vec<Constraint> = bel
                .iter()
                .map(|(s, v)| Constraint::Slot(*s, v.clone()))
                .collect();
            m = self.private(&m, *a, cs)?;
        }
        Ok(m)
    }

    fn slot_name(&self, s: usize) -> String {
        let sl = &self.world().slots[s];
        if sl.args.is_empty() {
            sl.fact.clone()
        } else {
            format!(
                "{}({})",
                sl.fact,
                sl.args
                    .iter()
                    .map(|a| self.prog.show(a))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }

    fn hidden_part(&self, ev: &Ev, env: &Env, e: &E) -> Result<(usize, Option<usize>), String> {
        match &e.kind {
            ExprKind::Field(b, f) => {
                let (s, _) = self.hidden_part(ev, env, b)?;
                let fact = &self.world().facts[&self.world().slots[s].fact];
                match &fact.ty {
                    Ty::Record(_, fs) => {
                        let i = fs
                            .iter()
                            .position(|(n, _)| n == f)
                            .ok_or(format!("no field '{}'", f))?;
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
            Who::Everyone => world.groups["Agent"]
                .iter()
                .map(|a| (*a, env.clone()))
                .collect(),
            Who::Nobody => vec![],
            Who::Agent(e) => match ev.eval(w, env, e)? {
                Value::Agent(aw, a) if aw as usize == self.wid => vec![(a, env.clone())],
                Value::Unknown => vec![],
                v => {
                    return Err(format!(
                        "'{}' is {}, not an agent of this world",
                        self.prog.text(e.span),
                        self.prog.show(&v)
                    ))
                }
            },
            Who::Every { ty, var, cond } => {
                let g = ty.clone().unwrap_or("Agent".into());
                let members = world
                    .groups
                    .get(&g)
                    .ok_or(format!("unknown group '{}'", g))?;
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
        let info = self
            .world()
            .actions
            .get(&*a.name)
            .ok_or(format!("unknown action '{}'", a.name))?;
        Ok(info
            .params
            .iter()
            .zip(a.args.iter())
            .map(|((n, _), v)| (Rc::from(n.as_str()), v.clone()))
            .collect())
    }

    /// Instantiate an action call written in the timeline or a rule.
    pub fn instantiate(
        &self,
        m: &Model,
        w: u32,
        c: &Call,
        env: &Env,
    ) -> Result<ActionInst, String> {
        let info = self
            .world()
            .actions
            .get(&c.name)
            .ok_or(format!("unknown action '{}'", c.name))?;
        if info.params.len() != c.args.len() {
            return Err(format!(
                "{} takes {} argument(s)",
                c.name,
                info.params.len()
            ));
        }
        let ev = self.ev(m);
        let mut args = vec![];
        for ((_, ty), e) in info.params.iter().zip(c.args.iter()) {
            let v = if *ty == Ty::Content {
                let is_event = match &e.kind {
                    ExprKind::SeenAs { .. } => true,
                    ExprKind::Name(_) | ExprKind::Qualified(..) => {
                        matches!(ev.eval(w, env, e), Ok(Value::Event(_)))
                    }
                    _ => false,
                };
                if is_event {
                    ev.eval(w, env, e)?
                } else {
                    Value::Formula(Rc::new(FormulaVal {
                        expr: e.clone(),
                        env: env.clone(),
                        world: self.wid,
                    }))
                }
            } else {
                coerce(self.world(), ty, ev.eval(w, env, e)?)
            };
            args.push(v);
        }
        Ok(ActionInst {
            name: Rc::from(c.name.as_str()),
            args,
        })
    }

    // ------------------------------------------------------------ views

    fn observer_views(
        &self,
        m: &Model,
        s: &EvScen,
        w: u32,
    ) -> Result<Vec<Option<Vec<View>>>, String> {
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
                        let secret = it.mods.iter().any(|m| matches!(m, Modifier::Secretly(_)));
                        let known_to = self.secret_except(&ev, w, &env, &it.mods)?;
                        let mut views = vec![View::Full {
                            secret,
                            known_to: known_to.clone(),
                        }];
                        for md in &it.mods {
                            match md {
                                Modifier::As(calls) => {
                                    let mut acts = vec![];
                                    for c in calls {
                                        acts.push(self.instantiate(m, w, c, &env)?);
                                    }
                                    views = vec![View::Acts {
                                        acts,
                                        step_clauses: false,
                                        secret,
                                        known_to: known_to.clone(),
                                    }];
                                }
                                Modifier::Hiding(e) => {
                                    let p = match &e.kind {
                                        ExprKind::Name(p) => p.clone(),
                                        _ => return Err("after `hiding` in an event, name one of the action's parameters".into()),
                                    };
                                    let expanded = self.expand_hidden(&s.actions, &[p])?;
                                    views = expanded
                                        .into_iter()
                                        .map(|acts| View::Acts {
                                            acts,
                                            step_clauses: true,
                                            secret,
                                            known_to: known_to.clone(),
                                        })
                                        .collect();
                                }
                                Modifier::Secretly(_) => {}
                            }
                        }
                        out[a as usize] = Some(views);
                    }
                }
            }
            None => {
                // per action defaults
                // per observer: (action index, hidden params, secret, what it looks like)
                #[allow(clippy::type_complexity)]
                let mut seen: Vec<Vec<(usize, Vec<String>, bool, Option<Vec<ActionInst>>)>> =
                    vec![vec![]; na];
                let mut known: Vec<Vec<u32>> = vec![vec![]; na];
                for (k, act) in s.actions.iter().enumerate() {
                    let info = world
                        .actions
                        .get(&*act.name)
                        .ok_or(format!("unknown action '{}'", act.name))?;
                    let env = self.action_env(act)?;
                    if let Some(items) = &info.seen_by {
                        for it in items {
                            for (a, env2) in self.who(&ev, w, &env, &it.who)? {
                                let secret =
                                    it.mods.iter().any(|m| matches!(m, Modifier::Secretly(_)));
                                known[a as usize].extend(
                                    self.secret_except(&ev, w, &env2, &it.mods)?.iter().copied(),
                                );
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
                                // an appearance: the action looks like something else
                                // to this observer, in this world
                                let mut looks = None;
                                for md in &it.mods {
                                    if let Modifier::As(calls) = md {
                                        let mut acts = vec![];
                                        for c in calls {
                                            acts.push(self.instantiate(m, w, c, &env2)?);
                                        }
                                        looks = Some(acts);
                                    }
                                }
                                seen[a as usize].retain(|x| x.0 != k);
                                seen[a as usize].push((k, hidden, secret, looks));
                            }
                        }
                    }
                }
                for a in 0..na {
                    if seen[a].is_empty() {
                        continue;
                    }
                    let secret = seen[a].iter().any(|x| x.2);
                    let known_to: Rc<[u32]> = known[a].clone().into();
                    let full = seen[a].len() == s.actions.len()
                        && seen[a].iter().all(|x| x.1.is_empty() && x.3.is_none());
                    if full {
                        out[a] = Some(vec![View::Full { secret, known_to }]);
                    } else {
                        let mut ks: Vec<_> = seen[a].iter().collect();
                        ks.sort_by_key(|x| x.0);
                        let acts: Vec<ActionInst> = ks
                            .iter()
                            .flat_map(|x| match &x.3 {
                                Some(looks) => looks.clone(),
                                None => vec![s.actions[x.0].clone()],
                            })
                            .collect();
                        let hidden: Vec<String> = ks.iter().flat_map(|x| x.1.clone()).collect();
                        let expanded = self.expand_hidden(&acts, &hidden)?;
                        out[a] = Some(
                            expanded
                                .into_iter()
                                .map(|acts| View::Acts {
                                    acts,
                                    step_clauses: false,
                                    secret,
                                    known_to: known_to.clone(),
                                })
                                .collect(),
                        );
                    }
                }
            }
        }
        {
            let blind = self.blind.borrow();
            if !blind.is_empty() {
                for (a, o) in out.iter_mut().enumerate() {
                    if blind.contains(&(a as u32, s.at)) {
                        *o = None;
                    }
                }
            }
        }
        if s.filtered {
            for (a, o) in out.iter_mut().enumerate() {
                let secret = o
                    .as_ref()
                    .and_then(|v| v.first())
                    .map(|v| v.secret())
                    .unwrap_or(false);
                if secret && !s.keep_secret.contains(&(a as u32)) {
                    *o = None;
                }
            }
        }
        Ok(out)
    }

    /// What an agent who saw nothing at step t considers: nothing happened, or (for a
    /// logician) one of the actions that may happen unseen happened out of sight.
    fn quiet(&self, a: u32, t: usize) -> Vec<Scen> {
        let world = self.world();
        if !world.actions.values().any(|x| x.unseen) {
            return vec![Scen::Skip];
        }
        let mut out = vec![Scen::Quiet(t)];
        if world.agents[a as usize].mode == Mode::Logician {
            for inst in self.unseen_instances() {
                out.push(Scen::Ev(Rc::new(EvScen {
                    actions: vec![inst],
                    step: None,
                    keep_secret: vec![],
                    naive: vec![],
                    unseen_by: Some(a),
                    filtered: true,
                    extra_pre: vec![],
                    lenient: false,
                    ignore_needs: false,
                    at: t,
                    revise: false,
                })));
            }
        }
        out
    }

    /// Every instance of the actions that may happen unseen.
    fn unseen_instances(&self) -> Vec<ActionInst> {
        let world = self.world();
        let mut names: Vec<&String> = world
            .actions
            .iter()
            .filter(|(_, x)| x.unseen)
            .map(|(n, _)| n)
            .collect();
        names.sort();
        let mut out = vec![];
        for n in names {
            let info = &world.actions[n];
            let mut combos: Vec<Vec<Value>> = vec![vec![]];
            for (_, ty) in &info.params {
                let Some(dom) = domain_of(world, ty) else {
                    combos.clear();
                    break;
                };
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
            for args in combos {
                out.push(ActionInst {
                    name: Rc::from(n.as_str()),
                    args,
                });
            }
        }
        out
    }

    /// The agents named in `secretly except …`.
    fn secret_except(
        &self,
        ev: &Ev,
        w: u32,
        env: &Env,
        mods: &[Modifier],
    ) -> Result<Rc<[u32]>, String> {
        let mut out = vec![];
        for m in mods {
            if let Modifier::Secretly(ex) = m {
                for e in ex {
                    match ev.eval(w, env, e)? {
                        Value::Agent(aw, x) if aw as usize == self.wid => out.push(x),
                        v => {
                            return Err(format!(
                                "after `secretly except`, '{}' is {}, not an agent of this world",
                                self.prog.text(e.span),
                                self.prog.show(&v)
                            ))
                        }
                    }
                }
            }
        }
        Ok(out.into())
    }

    /// Replace hidden parameters by each possible value (small finite types) or by Unknown.
    fn expand_hidden(
        &self,
        acts: &[ActionInst],
        hidden: &[String],
    ) -> Result<Vec<Vec<ActionInst>>, String> {
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
                        Value::Agent(aw, x) if *aw as usize == self.wid => match world.agents
                            [*x as usize]
                            .person
                        {
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
        if let Some((xw, xa)) = x.as_agent() {
            if xw as usize == self.wid && self.distrust.borrow().contains(&(a, xa)) {
                return false;
            }
        }
        self.trusts_raw(m, a, x, w)
    }

    fn trusts_raw(&self, m: &Model, a: u32, x: &Value, w: u32) -> bool {
        let world = self.world();
        if !world.honest_relevant {
            return true;
        }
        let Some((xw, xa)) = x.as_agent() else {
            return true;
        };
        if xw as usize != self.wid {
            return true;
        }
        let Some(&slot) = world
            .slot_of
            .get(&("honest".to_string(), vec![Value::Agent(xw, xa)]))
        else {
            return true;
        };
        let succ = m.succ(a, w);
        if succ.is_empty() {
            return true;
        }
        !succ
            .iter()
            .all(|v| m.vals[*v as usize][slot] == Value::Bool(false))
    }

    /// A person ignores testimony that tells them nothing new, and testimony that
    /// contradicts what they believe, unless it is news about something that can change.
    fn contradicts_belief(&self, m: &Model, a: u32, w: u32, content: &Value) -> bool {
        let Value::Formula(f) = content else {
            return false;
        };
        let succ = m.succ(a, w);
        if succ.is_empty() {
            return false;
        }
        let ev = self.ev(m);
        let truths: Vec<Option<bool>> = succ
            .iter()
            .map(|v| ev.truth(*v, &f.env, &f.expr).ok())
            .collect();
        if truths.iter().all(|t| *t == Some(true)) {
            return true; // nothing new
        }
        truths.iter().all(|t| *t == Some(false))
            && self.change_literals(m, w, &f.env, &f.expr).is_none()
    }

    /// If `e` is a conjunction of literals about changeable facts (`f(x)`, `not f(x)`,
    /// `f(x) = v`), the slot assignments that make it true.
    pub fn change_literals(
        &self,
        m: &Model,
        w: u32,
        env: &Env,
        e: &E,
    ) -> Option<Vec<(usize, Value)>> {
        let world = self.world();
        let ev = self.ev(m);
        let mut parts = vec![];
        split_and(e, &mut parts);
        let mut out = vec![];
        for part in &parts {
            let (neg, inner) = match &part.kind {
                ExprKind::Not(x) => (true, x),
                _ => (false, part),
            };
            let (head, val) = match &inner.kind {
                ExprKind::Bin(BinOp::Eq, l, r) if !neg => (l, ev.eval(w, env, r).ok()?),
                _ => (inner, Value::Bool(!neg)),
            };
            let (name, args): (&String, &[E]) = match &head.kind {
                ExprKind::Name(n) if !env.iter().any(|(k, _)| &**k == n.as_str()) => (n, &[]),
                ExprKind::Call(n, a) => (n, a),
                _ => return None,
            };
            if !world.changeable.contains(name) {
                return None;
            }
            let argv = args
                .iter()
                .map(|x| ev.eval(w, env, x))
                .collect::<Result<Vec<_>, _>>()
                .ok()?;
            out.push((*world.slot_of.get(&(name.clone(), argv))?, val));
        }
        Some(out)
    }

    /// If an action is a saying, the position of what is said. An action is a saying
    /// when its first parameter is an agent (the speaker) and it has an untyped
    /// parameter called `content`, like `tell` and `announce` in std.
    pub fn content_index(&self, name: &str) -> Option<usize> {
        let info = self.world().actions.get(name)?;
        if !matches!(info.params.first(), Some((_, Ty::Group(_)))) {
            return None;
        }
        info.params.iter().position(|(n, t)| n == "content" && *t == Ty::Content)
    }

    /// Testimony in an action: (speaker, content formula).
    fn said<'v>(&self, act: &'v ActionInst) -> Option<(&'v Value, &'v Value)> {
        let i = self.content_index(&act.name)?;
        match act.args.get(i)? {
            Value::Formula(_) => Some((&act.args[0], &act.args[i])),
            _ => None,
        }
    }

    /// A telling about an event: (speaker, event).
    fn told_event<'v>(&self, act: &'v ActionInst) -> Option<(&'v Value, &'v Rc<EventRef>)> {
        let i = self.content_index(&act.name)?;
        match act.args.get(i)? {
            Value::Event(r) => Some((&act.args[0], r)),
            _ => None,
        }
    }

    fn testimony(&self, m: &Model, a: u32, acts: &[ActionInst], w: u32) -> Vec<Value> {
        if self.world().agents[a as usize].mode != Mode::Person {
            return vec![];
        }
        let mut out = vec![];
        for act in acts {
            if let Some((teller_v, content)) = self.said(act) {
                {
                    let teller = teller_v.as_agent();
                    let world = self.world();
                    let same_person = |x: u32| {
                        world.agents[x as usize].person.unwrap_or(x)
                            == world.agents[a as usize].person.unwrap_or(a)
                    };
                    let own = matches!(teller, Some((tw, x)) if tw as usize == self.wid && (x == a || (same_person(x) && x == a)));
                    if !own && self.trusts(m, a, teller_v, w) && !self.contradicts_belief(m, a, w, content) {
                        out.push(content.clone());
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

    fn perceive_from_views(
        &self,
        m: &Model,
        a: u32,
        s: &EvScen,
        w: u32,
        views: &[Option<Vec<View>>],
    ) -> Result<Vec<Scen>, String> {
        let Some(vs) = &views[a as usize] else {
            return Ok(self.quiet(a, s.at));
        };
        // secret observers this agent is in on
        let mut in_on: Vec<u32> = vec![];
        for (b, bv) in views.iter().enumerate() {
            if let Some(first) = bv.as_ref().and_then(|x| x.first()) {
                if b as u32 != a
                    && first.secret()
                    && first.known_to().contains(&a)
                    && !s.naive.contains(&(b as u32))
                {
                    in_on.push(b as u32);
                }
            }
        }
        let mut out = vec![];
        for v in vs {
            let (acts, step, secret) = match v {
                View::Full { secret, .. } => (s.actions.clone(), s.step, *secret),
                View::Acts {
                    acts,
                    step_clauses,
                    secret,
                    ..
                } => (
                    acts.clone(),
                    if *step_clauses { s.step } else { None },
                    *secret,
                ),
            };
            let mut keep_secret = in_on.clone();
            let mut naive = s.naive.clone();
            if secret {
                keep_secret.push(a);
                if !naive.contains(&a) {
                    naive.push(a);
                }
            }
            let acts = self.map_segments(&acts, a);
            let extra_pre = if self.set_aside.borrow().contains(&(a, s.at)) {
                vec![]
            } else {
                self.testimony(m, a, &acts, w)
            };
            let lenient = self.world().agents[a as usize].mode == Mode::Person;
            out.push(Scen::Ev(Rc::new(EvScen {
                actions: acts,
                step,
                keep_secret,
                naive,
                unseen_by: None,
                filtered: true,
                extra_pre,
                lenient,
                ignore_needs: s.ignore_needs,
                at: s.at,
                revise: lenient && self.revise.borrow().contains(&(a, s.at)),
            })));
        }
        Ok(out)
    }

    /// The actions an agent believes happened in the real event (first reading).
    fn actual_view(
        &self,
        m: &Model,
        a: u32,
        real: &EvScen,
    ) -> Result<Option<Vec<ActionInst>>, String> {
        let ps = self.perceive_ev(m, a, real, m.actual)?;
        Ok(match ps.first() {
            Some(Scen::Ev(s)) => Some(s.actions.clone()),
            _ => None,
        })
    }

    // ------------------------------------------------------------ updates

    pub fn private(&self, m: &Model, agent: u32, cs: Vec<Constraint>) -> Result<Model, String> {
        let m = self.imagine(m, agent, &cs)?;
        let cs = Rc::new(cs);
        let mut sys = Sys {
            r: self,
            views: HashMap::new(),
        };
        let (m2, _) = product(&m, Scen::BelReal(agent, cs), &mut sys)?;
        Ok(contract(&m2))
    }

    /// How a conclusion updates its agent's beliefs.
    fn concl_constraints(&self, m: &Model, key: &CKey, f: Value) -> Vec<Constraint> {
        if self.as_change.borrow().contains(key) {
            if let Value::Formula(fv) = &f {
                if let Some(sets) = self.change_literals(m, m.actual, &fv.env, &fv.expr) {
                    return sets
                        .into_iter()
                        .map(|(s, v)| Constraint::Set(s, v))
                        .collect();
                }
            }
        }
        vec![Constraint::F(f)]
    }

    /// The agent forgets the value of a fact.
    pub fn forget(&self, m: &Model, agent: u32, slot: usize) -> Result<Model, String> {
        if !self.world().relevant.contains(&slot) {
            return Ok(m.clone());
        }
        let mut sys = Sys {
            r: self,
            views: HashMap::new(),
        };
        let (m2, _) = product(m, Scen::ForgetReal(agent, slot), &mut sys)?;
        Ok(contract(&m2))
    }

    /// Facts forgotten at a step: (agent, slot).
    fn forgotten_facts(&self, m: &Model, t: usize) -> Result<Vec<(u32, usize)>, String> {
        let st = &self.world().steps[t];
        let ev = self.ev(m);
        let mut out = vec![];
        for f in &st.forgets {
            let (aw, a) = ev
                .eval(m.actual, &st.env, &f.agent)?
                .as_agent()
                .ok_or(format!(
                    "line {}: expected an agent before `forgets`",
                    f.span.line
                ))?;
            if aw as usize != self.wid {
                return Err(format!(
                    "line {}: that agent isn't in this world",
                    f.span.line
                ));
            }
            if matches!(ev.eval(m.actual, &st.env, &f.what), Ok(Value::Event(_))) {
                continue;
            }
            let slot = self
                .target_slot(&ev, m.actual, &st.env, &f.what)
                .map_err(|e| format!("line {}: {}", f.span.line, e))?;
            out.push((a, slot));
        }
        Ok(out)
    }

    /// The watches in force after step t: (agent, slot).
    fn watched(&self, m: &Model, t: usize) -> Result<Vec<(u32, usize)>, String> {
        let world = self.world();
        let ev = self.ev(m);
        let mut out: Vec<(u32, usize)> = vec![];
        for st in &world.steps[..=t] {
            for wc in &st.watches {
                let (aw, a) = ev
                    .eval(m.actual, &st.env, &wc.agent)?
                    .as_agent()
                    .ok_or(format!(
                        "line {}: expected an agent before `watches`",
                        wc.span.line
                    ))?;
                if aw as usize != self.wid {
                    return Err(format!(
                        "line {}: that agent isn't in this world",
                        wc.span.line
                    ));
                }
                let slot = self
                    .target_slot(&ev, m.actual, &st.env, &wc.what)
                    .map_err(|e| format!("line {}: {}", wc.span.line, e))?;
                out.retain(|x| *x != (a, slot));
                if wc.on {
                    out.push((a, slot));
                }
            }
        }
        Ok(out)
    }

    /// Watchers see the current value of what they watch. A person who expected
    /// something else notices the change and assumes it happened out of sight.
    /// Returns the new model and the surprises: (agent, slot, new value).
    fn notice(&self, m: &Model, t: usize) -> Result<(Model, Vec<(u32, usize, Value)>), String> {
        let mut m = m.clone();
        let mut surprises = vec![];
        for (a, slot) in self.watched(&m, t)? {
            if !self.world().relevant.contains(&slot) {
                continue;
            }
            let v = m.vals[m.actual as usize][slot].clone();
            let succ = m.succ(a, m.actual).to_vec();
            let agree = succ
                .iter()
                .filter(|w| m.vals[**w as usize][slot] == v)
                .count();
            if agree == succ.len() {
                continue;
            }
            let c = if agree == 0 {
                surprises.push((a, slot, v.clone()));
                Constraint::Set(slot, v)
            } else {
                Constraint::Slot(slot, v)
            };
            m = self.private(&m, a, vec![c])?;
        }
        Ok((m, surprises))
    }

    /// The actor of an event: the first agent argument of its first action.
    fn actor(&self, m: &Model, t: usize) -> Option<u32> {
        let st = &self.world().steps[t];
        let c = st.actions.first()?;
        let act = self.instantiate(m, m.actual, c, &st.env).ok()?;
        match act.args.first() {
            Some(Value::Agent(aw, a)) if *aw as usize == self.wid => Some(*a),
            _ => None,
        }
    }

    /// For each constraint `b believes ψ` (b another agent here), the agent comes to
    /// think that b believes ψ: in the agent's worlds, b privately updates with ψ.
    pub fn imagine(&self, m: &Model, agent: u32, cs: &[Constraint]) -> Result<Model, String> {
        let mut m = m.clone();
        for c in cs {
            let Constraint::F(Value::Formula(f)) = c else {
                continue;
            };
            let ExprKind::Epistemic {
                agent: be,
                mode: KMode::Believes,
                body,
            } = &f.expr.kind
            else {
                continue;
            };
            let Ok(Value::Agent(bw, b)) = self.ev(&m).eval(m.actual, &f.env, be) else {
                continue;
            };
            if bw as usize != self.wid || b == agent {
                continue;
            }
            let inner = Value::Formula(Rc::new(FormulaVal {
                expr: body.clone(),
                env: f.env.clone(),
                world: f.world,
            }));
            let mut sys = Sys {
                r: self,
                views: HashMap::new(),
            };
            let (m2, _) = product(
                &m,
                Scen::NestReal(agent, b, Rc::new(vec![Constraint::F(inner)])),
                &mut sys,
            )?;
            m = contract(&m2);
        }
        Ok(m)
    }

    pub fn apply_event(
        &self,
        m: &Model,
        t: usize,
        mut diags: Option<&mut Vec<Diag>>,
    ) -> Result<EventOut, String> {
        let world = self.world();
        let st = &world.steps[t];
        let mut actions = vec![];
        for c in &st.actions {
            actions.push(
                self.instantiate(m, m.actual, c, &st.env)
                    .map_err(|e| format!("{}: {}", st.label, e))?,
            );
        }
        if let Some(sup) = self.suppress {
            if actions
                .iter()
                .any(|a| a.args.first() == Some(&Value::Agent(self.wid as u16, sup)))
            {
                let na = self.n_agents();
                return Ok(EventOut {
                    model: m.clone(),
                    actual: vec![],
                    views: vec![None; na],
                    triggered_errors: vec![],
                });
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
                        Ok(Some(false)) => {
                            broken = true;
                            if let Some(d) = diags.as_deref_mut() {
                                d.push(Diag {
                                    level: Level::Error,
                                    line: st.span.line,
                                    world: world.name.clone(),
                                    at: Some(st.label.clone()),
                                    msg: format!(
                                        "{} needs `{}`, which is false here",
                                        self.prog.show_action(act),
                                        self.prog.text(n.span)
                                    ),
                                })
                            }
                        }
                        Err(e) => return Err(format!("{}: {}", st.label, e)),
                        _ => {}
                    }
                }
            }
        }
        let real = Rc::new(EvScen {
            actions: actions.clone(),
            step: if st.seen_by.is_some() { Some(t) } else { None },
            keep_secret: vec![],
            naive: vec![],
            unseen_by: None,
            filtered: false,
            extra_pre: vec![],
            lenient: false,
            ignore_needs: broken,
            at: t,
            revise: false,
        });
        let na = self.n_agents();
        let mut views = vec![None; na];
        for a in 0..na as u32 {
            views[a as usize] = self.actual_view(m, a, &real)?;
        }
        let mut sys = Sys {
            r: self,
            views: HashMap::new(),
        };
        let (m2, nodes) =
            product(m, Scen::Ev(real), &mut sys).map_err(|e| format!("{}: {}", st.label, e))?;
        let mut actual = actions;
        let mut triggered_errors = vec![];
        let m3 = match self.rule_phase(&m2, &nodes)? {
            Some((m3, rounds)) => {
                for (rm, trig) in rounds {
                    let ev = self.ev(&rm);
                    // needs of triggered actions
                    for act in &trig {
                        let info = &world.actions[&*act.name];
                        let env = self.action_env(act)?;
                        for n in &info.needs {
                            if let Ok(Some(false)) = ev.strict_truth(rm.actual, &env, n) {
                                triggered_errors.push(format!(
                                    "{} needs `{}`, which is false here",
                                    self.prog.show_action(act),
                                    self.prog.text(n.span)
                                ));
                            }
                        }
                    }
                    // what each agent saw of the triggered actions
                    for act in &trig {
                        let info = &world.actions[&*act.name];
                        let env = self.action_env(act)?;
                        if let Some(items) = &info.seen_by {
                            for it in items {
                                for (a, _) in self.who(&ev, rm.actual, &env, &it.who)? {
                                    views[a as usize]
                                        .get_or_insert_with(Vec::new)
                                        .push(act.clone());
                                }
                            }
                        }
                    }
                    actual.extend(trig);
                }
                m3
            }
            None => m2,
        };
        Ok(EventOut {
            model: contract(&m3),
            actual,
            views,
            triggered_errors,
        })
    }

    /// Rules fire in every world; their actions become part of the event. Actions a
    /// rule triggers can trigger further rules. Returns the final model and, for each
    /// round, the model it fired in and the actions it triggered in the real world.
    #[allow(clippy::type_complexity)]
    fn rule_phase(
        &self,
        m: &Model,
        nodes: &[(u32, Scen)],
    ) -> Result<Option<(Model, Vec<(Model, Vec<ActionInst>)>)>, String> {
        let world = self.world();
        let do_rules: Vec<&RuleInfo> = world
            .rules
            .iter()
            .filter(|r| matches!((&r.trigger, &r.then), (Trigger::After(_), RuleThen::Do(_))))
            .collect();
        if do_rules.is_empty() {
            return Ok(None);
        }
        let mut acts: Vec<Vec<ActionInst>> = nodes
            .iter()
            .map(|(_, s)| match s {
                Scen::Ev(es) => es.actions.clone(),
                _ => vec![],
            })
            .collect();
        let mut cur = m.clone();
        let mut rounds = vec![];
        for _ in 0..8 {
            let trig = self.fire_rules(&cur, &do_rules, &acts)?;
            if trig.iter().all(|t| t.is_empty()) {
                return Ok(if rounds.is_empty() {
                    None
                } else {
                    Some((cur, rounds))
                });
            }
            let next = self.apply_triggered(&cur, &trig)?;
            rounds.push((cur, trig[m.actual as usize].clone()));
            acts = trig;
            cur = next;
        }
        Err("rules keep triggering each other (more than 8 rounds)".into())
    }

    fn fire_rules(
        &self,
        m: &Model,
        do_rules: &[&RuleInfo],
        acts: &[Vec<ActionInst>],
    ) -> Result<Vec<Vec<ActionInst>>, String> {
        let world = self.world();
        let ev = self.ev(m);
        let mut trig: Vec<Vec<ActionInst>> = vec![vec![]; m.n()];
        for (v, here) in acts.iter().enumerate() {
            for r in do_rules {
                let (Trigger::After(pat), RuleThen::Do(call)) = (&r.trigger, &r.then) else {
                    continue;
                };
                for act in here {
                    let Some(env) = self.match_pattern(&ev, v as u32, pat, act)? else {
                        continue;
                    };
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
                            Some(c) => ev
                                .truth(v as u32, &e2, c)
                                .map_err(|e| format!("rule {}: {}", r.name, e))?,
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
        Ok(trig)
    }

    /// Apply triggered actions in every world and refine relations by what each agent observes.
    fn apply_triggered(&self, m: &Model, trig: &[Vec<ActionInst>]) -> Result<Model, String> {
        let world = self.world();
        let ev = self.ev(m);
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
                rel[a][v] = m.rel[a][v]
                    .iter()
                    .copied()
                    .filter(|u| obs[*u as usize][a] == obs[v][a])
                    .collect();
            }
        }
        Ok(Model {
            vals,
            rel,
            actual: m.actual,
        })
    }

    fn match_pattern(
        &self,
        ev: &Ev,
        w: u32,
        pat: &Call,
        act: &ActionInst,
    ) -> Result<Option<Env>, String> {
        if pat.name != *act.name || pat.args.len() != act.args.len() {
            return Ok(None);
        }
        let world = self.world();
        let mut env: Env = vec![];
        for (p, v) in pat.args.iter().zip(act.args.iter()) {
            if let ExprKind::Name(n) = &p.kind {
                let bound = world.facts.contains_key(n)
                    || world.agent_names.contains_key(n)
                    || world.consts.contains_key(n)
                    || self.prog.params.contains_key(n);
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

    pub fn apply_effects_pub(
        &self,
        m: &Model,
        w: u32,
        act: &ActionInst,
        cur: &mut [Value],
    ) -> Result<(), String> {
        self.apply_effects(m, w, act, cur)
    }

    fn apply_effects(
        &self,
        m: &Model,
        w: u32,
        act: &ActionInst,
        cur: &mut [Value],
    ) -> Result<(), String> {
        let world = self.world();
        let info = &world.actions[&*act.name];
        let env = self.action_env(act)?;
        for eff in &info.effects {
            let snapshot: Vec<Value> = cur.to_vec();
            let ev = Ev {
                vals: Some(&snapshot),
                ..self.ev(m)
            };
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

    fn pending_conclusions(
        &self,
        m: &Model,
        t: usize,
        views: &[Option<Vec<ActionInst>>],
        actual: &[ActionInst],
    ) -> Result<Vec<PendingConcl>, String> {
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
            let RuleThen::Concludes(agent_e, f) = &r.then else {
                continue;
            };
            let candidates: Vec<(Option<u32>, Vec<ActionInst>)> = match &r.trigger {
                Trigger::After(_) => vec![(None, actual.to_vec())],
                Trigger::AfterSees(a, _) => {
                    let av = ev
                        .eval(m.actual, &vec![], a)?
                        .as_agent()
                        .ok_or("expected an agent")?;
                    vec![(Some(av.1), views[av.1 as usize].clone().unwrap_or_default())]
                }
            };
            let pat = match &r.trigger {
                Trigger::After(p) | Trigger::AfterSees(_, p) => p,
            };
            for (who, acts) in candidates {
                for act in &acts {
                    let Some(env) = self.match_pattern(&ev, m.actual, pat, act)? else {
                        continue;
                    };
                    let ok = match &r.when {
                        Some(c) => ev.truth(m.actual, &env, c)?,
                        None => true,
                    };
                    if ok {
                        out.push(PendingConcl {
                            key: (t, format!("r{}:{:?}", ri, env)),
                            agent_expr: if who.is_some() {
                                None
                            } else {
                                Some(agent_e.clone())
                            },
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
            _ => Err(format!(
                "'{}' is not an agent of this world",
                self.prog.text(e.span)
            )),
        }
    }

    /// Replay from the start, applying all conclusions except the disabled ones.
    pub fn simulate(
        &self,
        upto: usize,
        disabled: &HashSet<CKey>,
        include_last: bool,
    ) -> Result<Model, String> {
        let mut m = self.initial()?;
        for t in 0..=upto {
            let (views, actual) = if t > 0 {
                let out = self.apply_event(&m, t, None)?;
                m = out.model;
                (out.views, out.actual)
            } else {
                (vec![None; self.n_agents()], vec![])
            };
            m = self.notice(&m, t)?.0;
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
                let f = Value::Formula(Rc::new(FormulaVal {
                    expr: p.formula.clone(),
                    env: p.env.clone(),
                    world: self.wid,
                }));
                let cs = self.concl_constraints(&m, &p.key, f);
                m = self.private(&m, a, cs)?;
            }
            for (a, slot) in self.forgotten_facts(&m, t)? {
                m = self.forget(&m, a, slot)?;
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
            diags.push(Diag {
                level,
                line,
                world: world.name.clone(),
                at: Some(world.steps[t].label.clone()),
                msg,
            });
        };
        let mut model = match self.initial() {
            Ok(m) => m,
            Err(e) => {
                diags.push(Diag {
                    level: Level::Error,
                    line: world.steps[0].span.line,
                    world: world.name.clone(),
                    at: Some("start".into()),
                    msg: e,
                });
                return Run {
                    world: self.wid,
                    snaps,
                    diags,
                    conclusions: all_concl,
                    seg_beliefs: self.seg_beliefs.clone(),
                };
            }
        };
        let mut reg = Registry::new(na);
        let mut foreign_map: ForeignMap = ForeignMap::new();
        let mut disabled: HashSet<CKey> = self.pre_disabled.borrow().clone();
        let mut active: Vec<ConclRec> = vec![];
        let mut reported_empty_global: HashSet<u32> = HashSet::new();
        // agents already reported as having contradictory beliefs, until they recover
        let mut broken: HashSet<u32> = HashSet::new();

        for t in 0..world.steps.len() {
            let st = &world.steps[t];
            let mut views = vec![None; na];
            let mut actual = vec![];
            // wants stated at this step take effect now
            for wc in &st.wants {
                let ev = self.ev(&model);
                let a = match ev.eval(model.actual, &st.env, &wc.agent) {
                    Ok(Value::Agent(aw, a)) if aw as usize == self.wid => a,
                    _ => {
                        diag(
                            &mut diags,
                            Level::Error,
                            wc.span.line,
                            t,
                            format!(
                                "`{}` is not an agent of this world",
                                self.prog.text(wc.agent.span)
                            ),
                        );
                        continue;
                    }
                };
                let f = Value::Formula(Rc::new(FormulaVal {
                    expr: wc.formula.clone(),
                    env: st.env.clone(),
                    world: self.wid,
                }));
                let ws = &mut reg.wants[a as usize];
                let had = ws.iter().position(
                    |r| matches!(&r.formula, Value::Formula(g) if same_expr(&g.expr, &wc.formula)),
                );
                match (wc.on, had) {
                    (true, None) => ws.push(WantRec { formula: f }),
                    (false, Some(i)) => {
                        ws.remove(i);
                    }
                    (false, None) => diag(
                        &mut diags,
                        Level::Warning,
                        wc.span.line,
                        t,
                        format!(
                            "{} never wanted `{}`",
                            world.agents[a as usize].name,
                            self.prog.text(wc.formula.span)
                        ),
                    ),
                    _ => {}
                }
            }
            let actor = if t > 0 { self.actor(&model, t) } else { None };
            // so that: the actor must want it
            if let (Some(p), true) = (&st.purpose, t > 0) {
                match actor {
                    None => diag(&mut diags, Level::Error, st.span.line, t, "`so that` needs an actor: the first argument of the action should be the agent who acts".into()),
                    Some(a) => {
                        let wanted = reg.wants[a as usize].iter().any(|r| matches!(&r.formula, Value::Formula(g) if same_expr(&g.expr, p)));
                        if !wanted {
                            diag(&mut diags, Level::Error, st.span.line, t, format!("{} acts so that `{}`, but doesn't want it; add `{} wants {}` earlier", world.agents[a as usize].name, self.prog.text(p.span), world.agents[a as usize].name, self.prog.text(p.span)));
                        }
                    }
                }
            }
            // which of the actor's wants hold just before
            let wants_before: Vec<(Value, Option<bool>)> = match actor {
                Some(a) => reg.wants[a as usize]
                    .iter()
                    .map(|r| {
                        let ev = Ev {
                            registry: Some(&reg),
                            foreign: Some(&foreign_map),
                            ..self.ev(&model)
                        };
                        let held = match &r.formula {
                            Value::Formula(f) => ev
                                .strict_truth(model.actual, &f.env, &f.expr)
                                .ok()
                                .flatten(),
                            _ => None,
                        };
                        (r.formula.clone(), held)
                    })
                    .collect(),
                None => vec![],
            };
            if t > 0 {
                // because on the event itself, checked just before it
                for r in &st.reasons {
                    let ev = Ev {
                        registry: Some(&reg),
                        foreign: Some(&foreign_map),
                        ..self.ev(&model)
                    };
                    if let Some(msg) = reason_problem(self.prog, st, r) {
                        diag(&mut diags, Level::Error, st.span.line, t, msg);
                        continue;
                    }
                    match ev.strict_truth(model.actual, &st.env, &r.check) {
                        Ok(Some(false)) => diag(
                            &mut diags,
                            Level::Error,
                            st.span.line,
                            t,
                            reason_failed(self.prog, st, r),
                        ),
                        Err(e) => diag(&mut diags, Level::Error, st.span.line, t, e),
                        _ => {}
                    }
                }
                // telling about an event needs a view of it
                for c in &st.actions {
                    let Some(ci) = self.content_index(&c.name) else {
                        continue;
                    };
                    if let Ok(act) = self.instantiate(&model, model.actual, c, &st.env) {
                        if let (Some(Value::Agent(xw, x)), Some(Value::Event(r))) =
                            (act.args.first(), act.args.get(ci))
                        {
                            if self
                                .resolve_view(&reg, &foreign_map, (*xw, *x), r, None, &snaps)
                                .is_none()
                            {
                                diag(&mut diags, Level::Error, st.span.line, t, {
                                    let mut m = format!(
                                        "{} tells about {}, but never saw or heard of it",
                                        self.prog.agent_name(*xw, *x),
                                        self.prog.show(&act.args[ci])
                                    );
                                    if r.label == "start"
                                        && r.world == self.wid
                                        && !world.about.is_empty()
                                    {
                                        m.push_str(&format!(
                                            "; to tell about another world's start, write {}.start",
                                            self.prog.worlds[world.about[0]].name
                                        ));
                                    }
                                    m
                                });
                            }
                        }
                    }
                }
                let pre_model = model.clone();
                let errors_before = diags.iter().filter(|d| d.level == Level::Error).count();
                let mut result = self.apply_event(&model, t, Some(&mut diags));
                // a person who saw or heard something they thought impossible about a fact
                // that can change assumes it changed while they weren't looking
                loop {
                    let Ok(out) = &result else { break };
                    let stuck: Vec<u32> = (0..na as u32)
                        .filter(|&a| {
                            world.agents[a as usize].mode == Mode::Person
                                && out.model.succ(a, out.model.actual).is_empty()
                                && !model.succ(a, model.actual).is_empty()
                                && !self.revise.borrow().contains(&(a, t))
                        })
                        .collect();
                    if stuck.is_empty() {
                        break;
                    }
                    for &a in &stuck {
                        self.revise.borrow_mut().insert((a, t));
                    }
                    let retry = self.apply_event(&model, t, None);
                    let mut fixed = vec![];
                    if let Ok(o) = &retry {
                        for &a in &stuck {
                            if !o.model.succ(a, o.model.actual).is_empty() {
                                fixed.push(a);
                            }
                        }
                    }
                    if fixed.is_empty() {
                        for &a in &stuck {
                            self.revise.borrow_mut().remove(&(a, t));
                        }
                        break;
                    }
                    for &a in &stuck {
                        if !fixed.contains(&a) {
                            self.revise.borrow_mut().remove(&(a, t));
                        }
                    }
                    for &a in &fixed {
                        diag(&mut diags, Level::Note, st.span.line, t, format!("{} didn't expect this, and assumes things changed while they weren't looking", world.agents[a as usize].name));
                    }
                    result = self.apply_event(&model, t, None);
                    // conclusions the change has overtaken: true when drawn, no longer held
                    if let Ok(out) = &result {
                        let ev = self.ev(&out.model);
                        let mut i = 0;
                        while i < active.len() {
                            let c = &active[i];
                            let overtaken = fixed.contains(&c.agent)
                                && c.foreign.is_none()
                                && matches!(&c.formula, Value::Formula(f) if !ev.kripke_epistemic(out.model.actual, c.agent, KMode::Believes, &f.env, &f.expr).unwrap_or(true));
                            if overtaken {
                                let c = active.remove(i);
                                diag(&mut diags, Level::Note, c.line, t, format!("{} no longer believes `{}`: what they saw at {} shows it has changed", world.agents[c.agent as usize].name, self.prog.show(&c.formula), st.label));
                            } else {
                                i += 1;
                            }
                        }
                    }
                }
                match result {
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
                        reg.views[a].insert(
                            st.label.clone(),
                            ViewRec {
                                actions: v.clone(),
                                direct: true,
                                step: t,
                                actual: actual.clone(),
                            },
                        );
                    }
                }
                // second-hand views: tells whose content is an event
                for a in 0..na {
                    if world.agents[a].mode != Mode::Person {
                        continue;
                    }
                    let Some(v) = views[a].clone() else { continue };
                    for act in &v {
                        let Some((speaker, r)) = self.told_event(act) else {
                            continue;
                        };
                        let Some((xw, x)) = speaker.as_agent() else {
                            continue;
                        };
                        if !self.trusts(&pre_model, a as u32, &act.args[0], pre_model.actual) {
                            continue;
                        }
                        let Some(acts) =
                            self.resolve_view(&reg, &foreign_map, (xw, x), r, None, &snaps)
                        else {
                            continue;
                        };
                        self.adopt(
                            &mut reg,
                            &mut foreign_map,
                            &mut diags,
                            a as u32,
                            r.world,
                            &r.label,
                            acts,
                            t,
                            &snaps,
                            0,
                        );
                    }
                }
            }
            // retractions
            let mut reported_empty: HashSet<u32> = std::mem::take(&mut reported_empty_global);
            broken.retain(|a| model.succ(*a, model.actual).is_empty());
            reported_empty.extend(broken.iter().copied());
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
                        let fits = |m: &Model| -> Result<bool, String> {
                            Ok(!m.succ(a, m.actual).is_empty())
                        };
                        if let Ok(Some((m, dropped))) =
                            self.revise_by_recency(a, t, &reg, &active, &disabled, &fits)
                        {
                            let mut told_only = true;
                            for d in dropped {
                                match d {
                                    Revised::Concl(i) => {
                                        told_only = false;
                                        gone.push((
                                            i,
                                            format!("what they saw at {} contradicts it", st.label),
                                        ));
                                    }
                                    Revised::Told(step, x) => {
                                        self.set_aside.borrow_mut().insert((a, step));
                                        diag(&mut diags, Level::Note, st.span.line, t, format!("{} sets aside what {} told them at {}: what they saw at {} contradicts it", world.agents[a as usize].name, world.agents[x as usize].name, world.steps[step].label, st.label));
                                    }
                                }
                            }
                            if told_only {
                                model = m;
                                continue;
                            }
                            break;
                        }
                        reported_empty.insert(a);
                        broken.insert(a);
                        diag(&mut diags, Level::Error, st.span.line, t, format!("{}'s beliefs became contradictory: they saw something they thought impossible", world.agents[a as usize].name));
                    }
                }
                if gone.is_empty() {
                    break;
                }
                for (i, reason) in gone.iter().rev() {
                    let c = active.remove(*i);
                    disabled.insert(c.key.clone());
                    diag(
                        &mut diags,
                        Level::Note,
                        c.line,
                        t,
                        format!(
                            "{} no longer believes `{}`: {}",
                            world.agents[c.agent as usize].name,
                            self.prog.show(&c.formula),
                            reason
                        ),
                    );
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
                        if let Some(reason) = self.retraction_reason(&model, &reg, &foreign_map, c)
                        {
                            gone = Some((i, reason));
                            break;
                        }
                    }
                    let Some((i, reason)) = gone else { break };
                    let c = foreign_map.get_mut(&k).unwrap().active.remove(i);
                    diag(
                        &mut diags,
                        Level::Note,
                        c.line,
                        t,
                        format!(
                            "{} no longer believes `{}`: {}",
                            world.agents[c.agent as usize].name,
                            self.prog.show(&c.formula),
                            reason
                        ),
                    );
                }
            }
            // watchers see what they watch
            match self.notice(&model, t) {
                Ok((m, surprises)) => {
                    model = m;
                    for (a, slot, v) in surprises {
                        diag(
                            &mut diags,
                            Level::Note,
                            st.span.line,
                            t,
                            format!(
                                "{} notices `{}` is now {}, and assumes it changed out of sight",
                                world.agents[a as usize].name,
                                self.slot_name(slot),
                                self.prog.show(&v)
                            ),
                        );
                    }
                }
                Err(e) => diag(&mut diags, Level::Error, st.span.line, t, e),
            }
            // new conclusions
            let pending = match self.pending_conclusions(&model, t, &views, &actual) {
                Ok(p) => p,
                Err(e) => {
                    diag(&mut diags, Level::Error, st.span.line, t, e);
                    vec![]
                }
            };
            for (pi, p) in pending.iter().enumerate() {
                if disabled.contains(&p.key) && self.pre_disabled.borrow().contains(&p.key) {
                    continue;
                }
                let before = model.clone();
                match self.conclude(
                    &mut model,
                    &reg,
                    &mut foreign_map,
                    &mut active,
                    &mut disabled,
                    &mut diags,
                    t,
                    p,
                ) {
                    Ok(Some(rec)) => {
                        all_concl.push(rec);
                        let later: Vec<CKey> =
                            pending[pi + 1..].iter().map(|q| q.key.clone()).collect();
                        if let Err(e) = self.withdraw_testimony(
                            &before,
                            &mut model,
                            &reg,
                            &foreign_map,
                            &mut active,
                            &mut disabled,
                            &mut diags,
                            t,
                            &later,
                            &p.key,
                        ) {
                            diag(&mut diags, Level::Error, st.span.line, t, e);
                            return self.abort(snaps, diags, all_concl);
                        }
                    }
                    Ok(None) => {
                        disabled.insert(p.key.clone());
                    }
                    Err(e) => {
                        disabled.insert(p.key.clone());
                        diag(&mut diags, Level::Error, p.line, t, e);
                    }
                }
            }
            // forgetting
            for f in &st.forgets {
                let ev = self.ev(&model);
                if let (Ok(Value::Agent(aw, a)), Ok(Value::Event(r))) = (
                    ev.eval(model.actual, &st.env, &f.agent),
                    ev.eval(model.actual, &st.env, &f.what),
                ) {
                    if aw as usize == self.wid && r.world == self.wid {
                        if reg.views[a as usize].remove(&r.label).is_none() {
                            diag(
                                &mut diags,
                                Level::Warning,
                                f.span.line,
                                t,
                                format!(
                                    "{} forgets {}, which they never knew of",
                                    world.agents[a as usize].name, r.label
                                ),
                            );
                        }
                    }
                }
            }
            match self.forgotten_facts(&model, t) {
                Ok(fs) => {
                    for (a, slot) in fs {
                        match self.forget(&model, a, slot) {
                            Ok(m) => model = m,
                            Err(e) => diag(&mut diags, Level::Error, st.span.line, t, e),
                        }
                    }
                }
                Err(e) => diag(&mut diags, Level::Error, st.span.line, t, e),
            }
            // suspicions lapse when their source changes or the opposite is believed
            for a in 0..na {
                let mut keep = vec![];
                for r in std::mem::take(&mut reg.suspicions[a]) {
                    let mut why = None;
                    for (i, (_, label)) in r.sources.iter().enumerate() {
                        let now = reg.views[a].get(label).map(|v| v.actions.clone());
                        if now != r.snapshot[i] {
                            why = Some(format!(
                                "{} now looks like `{}`",
                                label,
                                now.map(|n| self.prog.show_actions(&n))
                                    .unwrap_or("nothing".into())
                            ));
                        }
                    }
                    if why.is_none() {
                        if let Value::Formula(f) = &r.formula {
                            let ev = Ev {
                                registry: Some(&reg),
                                foreign: Some(&foreign_map),
                                ..self.ev(&model)
                            };
                            if let Ok(true) = ev.kripke_epistemic(
                                model.actual,
                                a as u32,
                                KMode::Believes,
                                &f.env,
                                &Rc::new(Expr {
                                    kind: ExprKind::Not(f.expr.clone()),
                                    span: f.expr.span,
                                }),
                            ) {
                                why = Some("they now believe the opposite".into());
                            }
                        }
                    }
                    match why {
                        Some(w) => diag(
                            &mut diags,
                            Level::Note,
                            r.line,
                            t,
                            format!(
                                "{} no longer suspects `{}`: {}",
                                world.agents[a].name,
                                self.prog.show(&r.formula),
                                w
                            ),
                        ),
                        None => keep.push(r),
                    }
                }
                reg.suspicions[a] = keep;
            }
            for c in &st.suspicions {
                let ev = self.ev(&model);
                let a = match ev.eval(model.actual, &st.env, &c.agent) {
                    Ok(Value::Agent(aw, a)) if aw as usize == self.wid => a,
                    _ => {
                        diag(
                            &mut diags,
                            Level::Error,
                            c.span.line,
                            t,
                            format!(
                                "`{}` is not an agent of this world",
                                self.prog.text(c.agent.span)
                            ),
                        );
                        continue;
                    }
                };
                let mut parts = vec![];
                if let Some(b) = &c.because {
                    split_and(b, &mut parts);
                }
                let mut sources = vec![];
                let mut snapshot = vec![];
                let mut ok = true;
                for part in parts {
                    if let Ok(Value::Event(r)) = ev.eval(model.actual, &st.env, &part) {
                        let v = reg.views[a as usize]
                            .get(&r.label)
                            .map(|v| v.actions.clone());
                        if v.is_none() && r.world == self.wid {
                            diag(
                                &mut diags,
                                Level::Error,
                                c.span.line,
                                t,
                                format!(
                                    "{} suspects `{}` because of {}, but never saw or heard of {}",
                                    world.agents[a as usize].name,
                                    self.prog.text(c.formula.span),
                                    r.label,
                                    r.label
                                ),
                            );
                            ok = false;
                        }
                        sources.push((r.world, r.label.clone()));
                        snapshot.push(v);
                    }
                }
                if ok {
                    let f = Value::Formula(Rc::new(FormulaVal {
                        expr: c.formula.clone(),
                        env: st.env.clone(),
                        world: self.wid,
                    }));
                    reg.suspicions[a as usize].push(SuspRec {
                        formula: f,
                        sources,
                        snapshot,
                        line: c.span.line,
                    });
                }
            }
            // motives: did the actor undo something they want, or fail to get what they acted for?
            if let Some(a) = actor {
                let ev = Ev {
                    registry: Some(&reg),
                    foreign: Some(&foreign_map),
                    ..self.ev(&model)
                };
                for (f, before) in &wants_before {
                    let Value::Formula(fv) = f else { continue };
                    // they undid it, and can tell they did
                    let after = ev
                        .strict_truth(model.actual, &fv.env, &fv.expr)
                        .ok()
                        .flatten();
                    let not_f = Rc::new(Expr {
                        kind: ExprKind::Not(fv.expr.clone()),
                        span: fv.expr.span,
                    });
                    let sees_it = ev
                        .kripke_epistemic(model.actual, a, KMode::Believes, &fv.env, &not_f)
                        .unwrap_or(false);
                    if *before == Some(true)
                        && after == Some(false)
                        && sees_it
                        && st.because.is_none()
                        && st.purpose.is_none()
                    {
                        diag(&mut diags, Level::Warning, st.span.line, t, format!("{} acts against their own want `{}` with no reason given; add `because …` or `so that …`", world.agents[a as usize].name, self.prog.text(fv.expr.span)));
                    }
                }
                if let Some(p) = &st.purpose {
                    if let Ok(Some(false)) = ev.strict_truth(model.actual, &st.env, p) {
                        diag(
                            &mut diags,
                            Level::Note,
                            st.span.line,
                            t,
                            format!(
                                "{}'s plan hasn't worked yet: `{}` is false after {}",
                                world.agents[a as usize].name,
                                self.prog.text(p.span),
                                st.label
                            ),
                        );
                    }
                }
            }
            snaps.push(Snap {
                model: Rc::new(model.clone()),
                registry: Rc::new(reg.clone()),
                foreign: Rc::new(foreign_map.clone()),
                actual,
                disabled: Rc::new(disabled.clone()),
            });
        }
        Run {
            world: self.wid,
            snaps,
            diags,
            conclusions: all_concl,
            seg_beliefs: self.seg_beliefs.clone(),
        }
    }

    fn abort(&self, snaps: Vec<Snap>, mut diags: Vec<Diag>, concl: Vec<ConclRec>) -> Run {
        let world = self.world();
        diags.push(Diag {
            level: Level::Note,
            line: 0,
            world: world.name.clone(),
            at: None,
            msg: "checking of this world stopped here".into(),
        });
        Run {
            world: self.wid,
            snaps,
            diags,
            conclusions: concl,
            seg_beliefs: self.seg_beliefs.clone(),
        }
    }

    /// The view a teller would pass on.
    fn resolve_view(
        &self,
        reg: &Registry,
        fm: &ForeignMap,
        teller: (u16, u32),
        r: &EventRef,
        at_step: Option<usize>,
        snaps: &[Snap],
    ) -> Option<Vec<ActionInst>> {
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
            return g
                .views
                .get(s as usize)?
                .get(&r.label)
                .map(|v| v.actions.clone());
        }
        let (tw, x) = (teller.0 as usize, teller.1);
        if tw == self.wid {
            if r.world == self.wid {
                return reg.views[x as usize]
                    .get(&r.label)
                    .map(|v| v.actions.clone());
            }
            if prog.worlds[tw].agents[x as usize].sees_all_of == Some(r.world) {
                return self.hub.snap(r.world, estep).map(|s| s.actual.clone());
            }
            return fm
                .get(&(x, r.world))
                .and_then(|f| f.views.get(&r.label))
                .map(|v| v.0.clone());
        }
        // a teller inside another world, at the time they told it
        let step = at_step?;
        let g = reg_at(tw, step)?;
        g.views
            .get(x as usize)?
            .get(&r.label)
            .map(|v| v.actions.clone())
    }

    #[allow(clippy::too_many_arguments)]
    fn adopt(
        &self,
        reg: &mut Registry,
        fm: &mut ForeignMap,
        diags: &mut Vec<Diag>,
        a: u32,
        ew: usize,
        label: &str,
        acts: Vec<ActionInst>,
        t: usize,
        snaps: &[Snap],
        depth: usize,
    ) {
        let world = self.world();
        let st = &world.steps[t];
        let estep = match self.prog.worlds[ew].label_index.get(label) {
            Some(s) => *s,
            None => return,
        };
        let old: Option<Vec<ActionInst>> = if ew == self.wid {
            reg.views[a as usize].get(label).map(|v| v.actions.clone())
        } else {
            fm.get(&(a, ew))
                .and_then(|f| f.views.get(label))
                .map(|v| v.0.clone())
        };
        // a conflicting account is accepted when the author resolves it here, with a
        // conclusion of this agent that rests on the event
        let resolved = st.conclusions.iter().any(|c| {
            let mut parts = vec![];
            if let Some(b) = &c.because {
                split_and(b, &mut parts);
            }
            self.prog.text(c.agent.span) == world.agents[a as usize].name
                && parts.iter().any(|p| match &p.kind {
                    ExprKind::Name(n) => n == label,
                    ExprKind::Qualified(_, n) => n == label,
                    _ => false,
                })
        });
        if let Some(old) = &old {
            if !contains(&acts, old) && !resolved {
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
            let actual = snaps
                .get(estep)
                .map(|s| s.actual.clone())
                .unwrap_or_default();
            reg.views[a as usize].insert(
                label.to_string(),
                ViewRec {
                    actions: acts.clone(),
                    direct: false,
                    step: estep,
                    actual,
                },
            );
        } else {
            let entry = fm.entry((a, ew)).or_default();
            entry.views.insert(label.to_string(), (acts.clone(), estep));
            if estep == 0 {
                // how things stood at the start, as an all-seeing narrator knows it
                if let Some(snap) = self.hub.snap(ew, 0) {
                    let ow = &self.prog.worlds[ew];
                    let vals = &snap.model.vals[snap.model.actual as usize];
                    for &slot in &ow.relevant {
                        entry.facts.insert(slot, vals[slot].clone());
                    }
                }
            }
        }
        if depth > 4 {
            return;
        }
        // nested tellings inside the adopted view
        for act in &acts {
            let Some((speaker, r)) = self.told_event(act) else {
                continue;
            };
            let Some(teller) = speaker.as_agent() else {
                continue;
            };
            let inner = self.resolve_view(reg, fm, teller, r, Some(estep), snaps);
            if let Some(inner) = inner {
                self.adopt(
                    reg,
                    fm,
                    diags,
                    a,
                    r.world,
                    &r.label,
                    inner,
                    t,
                    snaps,
                    depth + 1,
                );
            }
        }
    }

    /// Revise a person's beliefs by recency. The candidates are their own conclusions and
    /// the testimony they accepted. All are dropped, then each is kept back, newest first
    /// (at the same step, a conclusion before testimony), while `fits` still holds.
    /// Returns the model and what had to go, or None if dropping everything isn't enough.
    #[allow(clippy::too_many_arguments)]
    fn revise_by_recency(
        &self,
        a: u32,
        t: usize,
        reg: &Registry,
        active: &[ConclRec],
        disabled: &HashSet<CKey>,
        fits: &dyn Fn(&Model) -> Result<bool, String>,
    ) -> Result<Option<(Model, Vec<Revised>)>, String> {
        let mut items: Vec<(usize, u8, Revised)> = vec![];
        for (i, c) in active.iter().enumerate() {
            if c.agent == a && c.foreign.is_none() {
                items.push((c.step, 0, Revised::Concl(i)));
            }
        }
        let mut told: Vec<(usize, u32)> = vec![];
        for v in reg.views[a as usize].values() {
            for act in &v.actions {
                if self.said(act).is_some() {
                    if let Some((xw, x)) = act.args.first().and_then(|v| v.as_agent()) {
                        if xw as usize == self.wid
                            && x != a
                            && !self.set_aside.borrow().contains(&(a, v.step))
                        {
                            told.push((v.step, x));
                        }
                    }
                }
            }
        }
        told.sort_unstable();
        told.dedup_by_key(|x| x.0);
        for (step, x) in told {
            items.push((step, 1, Revised::Told(step, x)));
        }
        if items.is_empty() {
            return Ok(None);
        }
        items.sort_by(|x, y| y.0.cmp(&x.0).then(x.1.cmp(&y.1)));
        let order: Vec<Revised> = items.into_iter().map(|x| x.2).collect();
        let sim = |dropped: &[Revised]| -> Result<Model, String> {
            let mut dis = disabled.clone();
            let mut added = vec![];
            for d in dropped {
                match d {
                    Revised::Concl(i) => {
                        dis.insert(active[*i].key.clone());
                    }
                    Revised::Told(step, _) => {
                        if self.set_aside.borrow_mut().insert((a, *step)) {
                            added.push(*step);
                        }
                    }
                }
            }
            let r = (|| {
                let mut m = self.simulate(t, &dis, false)?;
                for c in active
                    .iter()
                    .filter(|c| c.step == t && !dis.contains(&c.key) && c.foreign.is_none())
                {
                    let cs = self.concl_constraints(&m, &c.key, c.formula.clone());
                    m = self.private(&m, c.agent, cs)?;
                }
                Ok(m)
            })();
            for step in added {
                self.set_aside.borrow_mut().remove(&(a, step));
            }
            r
        };
        let mut dropped = order.clone();
        let mut m = sim(&dropped)?;
        if !fits(&m)? {
            return Ok(None);
        }
        for it in &order {
            let trial: Vec<Revised> = dropped.iter().copied().filter(|d| d != it).collect();
            let m2 = sim(&trial)?;
            if fits(&m2)? {
                dropped = trial;
                m = m2;
            }
        }
        Ok(Some((m, dropped)))
    }

    /// A person who has just come to believe `not honest(x)` withdraws everything x
    /// told them, and every conclusion drawn from x's tellings. History is replayed
    /// without that testimony; conclusions later in this step are left for the caller.
    #[allow(clippy::too_many_arguments)]
    fn withdraw_testimony(
        &self,
        before: &Model,
        model: &mut Model,
        reg: &Registry,
        fm: &ForeignMap,
        active: &mut Vec<ConclRec>,
        disabled: &mut HashSet<CKey>,
        diags: &mut Vec<Diag>,
        t: usize,
        later: &[CKey],
        trigger: &CKey,
    ) -> Result<(), String> {
        let world = self.world();
        let na = self.n_agents() as u32;
        let mut newly = vec![];
        for a in 0..na {
            if world.agents[a as usize].mode != Mode::Person {
                continue;
            }
            for x in 0..na {
                if x == a || self.distrust.borrow().contains(&(a, x)) {
                    continue;
                }
                let xv = Value::Agent(self.wid as u16, x);
                if !self.trusts_raw(model, a, &xv, model.actual)
                    && self.trusts_raw(before, a, &xv, before.actual)
                {
                    newly.push((a, x));
                }
            }
        }
        if newly.is_empty() {
            return Ok(());
        }
        self.distrust.borrow_mut().extend(newly.iter().copied());
        let line = world.steps[t].span.line;
        let note = |diags: &mut Vec<Diag>, l: usize, msg: String| {
            diags.push(Diag {
                level: Level::Note,
                line: l,
                world: world.name.clone(),
                at: Some(world.steps[t].label.clone()),
                msg,
            });
        };
        for (a, x) in &newly {
            let told = reg.views[*a as usize].values().any(|v| {
                v.actions.iter().any(|act| {
                    self.said(act).is_some()
                        && act.args.first().and_then(|v| v.as_agent())
                            == Some((self.wid as u16, *x))
                })
            });
            if told {
                note(
                    diags,
                    line,
                    format!(
                        "{} no longer trusts {}, and withdraws what {} told them",
                        world.agents[*a as usize].name,
                        world.agents[*x as usize].name,
                        world.agents[*x as usize].name
                    ),
                );
            }
        }
        let mut extra: HashSet<CKey> = disabled.clone();
        extra.extend(later.iter().cloned());
        let from_teller = |c: &ConclRec| -> Option<u32> {
            if &c.key == trigger {
                return None;
            }
            for (ew, label) in &c.event_sources {
                if *ew != self.wid || c.despite.contains(&(*ew, label.clone())) {
                    continue;
                }
                let Some(v) = reg.views[c.agent as usize].get(label) else {
                    continue;
                };
                for act in &v.actions {
                    if self.said(act).is_none() {
                        continue;
                    }
                    if let Some((_, x)) = act.args.first().and_then(|v| v.as_agent()) {
                        if newly.contains(&(c.agent, x)) {
                            return Some(x);
                        }
                    }
                }
            }
            None
        };
        let mut i = 0;
        while i < active.len() {
            if let Some(x) = from_teller(&active[i]) {
                let c = active.remove(i);
                disabled.insert(c.key.clone());
                extra.insert(c.key.clone());
                note(
                    diags,
                    c.line,
                    format!(
                        "{} no longer believes `{}`: it came from {}, whom they no longer trust",
                        world.agents[c.agent as usize].name,
                        self.prog.show(&c.formula),
                        world.agents[x as usize].name
                    ),
                );
            } else {
                i += 1;
            }
        }
        *model = self.simulate(t, &extra, true)?;
        // cascade through beliefs that rested on what was withdrawn
        loop {
            let Some(i) = active
                .iter()
                .position(|c| self.retraction_reason(model, reg, fm, c).is_some())
            else {
                break;
            };
            let reason = self.retraction_reason(model, reg, fm, &active[i]).unwrap();
            let c = active.remove(i);
            disabled.insert(c.key.clone());
            extra.insert(c.key.clone());
            note(
                diags,
                c.line,
                format!(
                    "{} no longer believes `{}`: {}",
                    world.agents[c.agent as usize].name,
                    self.prog.show(&c.formula),
                    reason
                ),
            );
            *model = self.simulate(t, &extra, true)?;
        }
        Ok(())
    }

    fn retraction_reason(
        &self,
        m: &Model,
        reg: &Registry,
        fm: &ForeignMap,
        c: &ConclRec,
    ) -> Option<String> {
        for (i, (ew, label)) in c.event_sources.iter().enumerate() {
            if c.despite.contains(&(*ew, label.clone())) {
                continue;
            }
            let now: Option<Vec<ActionInst>> = if *ew == self.wid {
                reg.views[c.agent as usize]
                    .get(label)
                    .map(|v| v.actions.clone())
            } else {
                fm.get(&(c.agent, *ew))
                    .and_then(|f| f.views.get(label))
                    .map(|v| v.0.clone())
            };
            if now != c.snapshot[i] {
                let shown = now
                    .map(|n| self.prog.show_actions(&n))
                    .unwrap_or("nothing".into());
                return Some(format!("{} now looks like `{}`", label, shown));
            }
        }
        for b in &c.belief_sources {
            let Value::Formula(f) = b else { continue };
            let held = match c.foreign {
                Some(tw) => foreign::believes(
                    self.prog,
                    tw,
                    &fm.get(&(c.agent, tw)).cloned().unwrap_or_default(),
                    &f.env,
                    &f.expr,
                ),
                None => {
                    let ev = self.ev(m);
                    match ev.foreign_world(&f.expr) {
                        Ok(Some(tw)) => foreign::believes(
                            self.prog,
                            tw,
                            &fm.get(&(c.agent, tw)).cloned().unwrap_or_default(),
                            &f.env,
                            &f.expr,
                        ),
                        _ => ev
                            .kripke_epistemic(m.actual, c.agent, KMode::Believes, &f.env, &f.expr)
                            .unwrap_or(true),
                    }
                }
            };
            if !held {
                return Some(format!(
                    "it rested on `{}`, which they no longer believe",
                    self.prog.text(f.expr.span)
                ));
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
        let fval = Value::Formula(Rc::new(FormulaVal {
            expr: p.formula.clone(),
            env: p.env.clone(),
            world: self.wid,
        }));
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
                _ => belief_sources.push(Value::Formula(Rc::new(FormulaVal {
                    expr: part.clone(),
                    env: p.env.clone(),
                    world: self.wid,
                }))),
            }
        }
        let mut despite = vec![];
        if let Some(d) = &p.despite {
            let mut ds = vec![];
            split_and(d, &mut ds);
            for part in ds {
                match ev.eval(model.actual, &p.env, &part) {
                    Ok(Value::Event(r)) => despite.push((r.world, r.label.clone())),
                    _ => {
                        return Err(format!(
                            "after `despite`, name an event (got `{}`)",
                            self.prog.text(part.span)
                        ))
                    }
                }
            }
        }
        // check sources
        let view_of = |fm: &ForeignMap, ew: usize, label: &str| -> Option<Vec<ActionInst>> {
            if ew == self.wid {
                reg.views[a as usize].get(label).map(|v| v.actions.clone())
            } else {
                fm.get(&(a, ew))
                    .and_then(|f| f.views.get(label))
                    .map(|v| v.0.clone())
            }
        };
        let mut snapshot = vec![];
        for (ew, label) in event_sources.iter().chain(despite.iter()) {
            let v = view_of(fm, *ew, label);
            if v.is_none() {
                return Err(format!(
                    "{} concludes `{}` because of {}, but never saw or heard of {}",
                    aname,
                    self.prog.text(p.formula.span),
                    label,
                    label
                ));
            }
        }
        for (ew, label) in &event_sources {
            snapshot.push(view_of(fm, *ew, label));
        }
        for b in &belief_sources {
            let Value::Formula(f) = b else { continue };
            let held = match ev.foreign_world(&f.expr)? {
                Some(fw) => foreign::believes(
                    self.prog,
                    fw,
                    &fm.get(&(a, fw)).cloned().unwrap_or_default(),
                    &f.env,
                    &f.expr,
                ),
                None => ev.kripke_epistemic(model.actual, a, KMode::Believes, &f.env, &f.expr)?,
            };
            if !held {
                return Err(format!(
                    "{} concludes `{}` because `{}`, but doesn't believe that",
                    aname,
                    self.prog.text(p.formula.span),
                    self.prog.text(f.expr.span)
                ));
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
                let mut trial = ForeignStore {
                    views: st.views.clone(),
                    facts: st.facts.clone(),
                    active: vec![],
                };
                for c in kept {
                    trial.active.push(c.clone());
                    if foreign::believes_not(self.prog, tw, &trial, &p.env, &p.formula) {
                        trial.active.pop();
                        diags.push(Diag {
                            level: Level::Note,
                            line: p.line,
                            world: world.name.clone(),
                            at: Some(world.steps[t].label.clone()),
                            msg: format!(
                                "{} revises: drops `{}`",
                                aname,
                                self.prog.show(&c.formula)
                            ),
                        });
                    }
                }
                st.active = trial.active;
                let _ = before;
                if foreign::believes_not(self.prog, tw, st, &p.env, &p.formula) {
                    return Err(format!(
                        "{} concludes `{}`, but what they were told rules it out",
                        aname,
                        self.prog.text(p.formula.span)
                    ));
                }
            }
            st.active.push(rec.clone());
            return Ok(Some(rec));
        }
        // consistency with current beliefs; revise own conclusions if needed
        let consistent = |m: &Model| -> Result<bool, String> {
            let m = &self.imagine(m, a, &[Constraint::F(fval.clone())])?;
            let ev = self.ev(m);
            for &v in m.succ(a, m.actual) {
                if ev.truth(v, &p.env, &p.formula)? {
                    return Ok(true);
                }
            }
            Ok(false)
        };
        if !consistent(model)? {
            let fits = |m: &Model| consistent(m);
            match self.revise_by_recency(a, t, reg, active, disabled, &fits)? {
                Some((m, dropped)) => {
                    *model = m;
                    let mut gone: Vec<usize> = vec![];
                    for d in dropped {
                        match d {
                            Revised::Concl(i) => gone.push(i),
                            Revised::Told(step, x) => {
                                self.set_aside.borrow_mut().insert((a, step));
                                diags.push(Diag {
                                    level: Level::Note,
                                    line: p.line,
                                    world: world.name.clone(),
                                    at: Some(world.steps[t].label.clone()),
                                    msg: format!(
                                        "{} sets aside what {} told them at {}",
                                        aname,
                                        world.agents[x as usize].name,
                                        world.steps[step].label
                                    ),
                                });
                            }
                        }
                    }
                    gone.sort_unstable();
                    for i in gone.into_iter().rev() {
                        let c = active.remove(i);
                        disabled.insert(c.key.clone());
                        diags.push(Diag {
                            level: Level::Note,
                            line: p.line,
                            world: world.name.clone(),
                            at: Some(world.steps[t].label.clone()),
                            msg: format!(
                                "{} revises: drops `{}`",
                                aname,
                                self.prog.show(&c.formula)
                            ),
                        });
                    }
                }
                None => {
                    // about something that can change: they conclude it has changed
                    if let Value::Formula(fv) = &fval {
                        if let Some(sets) =
                            self.change_literals(model, model.actual, &fv.env, &fv.expr)
                        {
                            self.as_change.borrow_mut().insert(p.key.clone());
                            *model = self.private(
                                model,
                                a,
                                sets.into_iter()
                                    .map(|(s, v)| Constraint::Set(s, v))
                                    .collect(),
                            )?;
                            active.push(rec.clone());
                            return Ok(Some(rec));
                        }
                    }
                    return Err(format!(
                        "{} concludes `{}`, but what they have seen rules it out",
                        aname,
                        self.prog.text(p.formula.span)
                    ));
                }
            }
        }
        *model = self.private(model, a, vec![Constraint::F(fval)])?;
        active.push(rec.clone());
        Ok(Some(rec))
    }
}

/// A reason Ken can't check: one about another person's wants, suspicions or
/// sightings, which can't be nested inside the actor's beliefs.
pub fn reason_problem(prog: &Program, st: &Step, r: &Reason) -> Option<String> {
    let holder = r.holder.as_ref()?;
    fn nests(e: &E) -> bool {
        match &e.kind {
            ExprKind::Not(x) => nests(x),
            ExprKind::Bin(_, a, b) => nests(a) || nests(b),
            ExprKind::Wants { .. } | ExprKind::Suspects { .. } | ExprKind::Saw { .. } => true,
            _ => false,
        }
    }
    if !nests(&r.part) {
        return None;
    }
    Some(format!(
        "{} happens because `{}`, but a reason for acting must be in {}'s head, and Ken can't put someone else's wants, suspicions or sightings there. Give a reason {} could hold, e.g. `because {} believes …`",
        st.label,
        prog.text(r.part.span),
        prog.text(holder.span),
        prog.text(holder.span),
        prog.text(holder.span)
    ))
}

/// The message for a reason that doesn't hold just before its event.
pub fn reason_failed(prog: &Program, st: &Step, r: &Reason) -> String {
    match &r.holder {
        None => format!(
            "this happens because `{}`, but that isn't true just before {}",
            prog.text(r.part.span),
            st.label
        ),
        Some(h) => format!(
            "this happens because `{}`, but {} doesn't believe that just before {}: a reason for acting must be in the actor's head",
            prog.text(r.part.span),
            prog.text(h.span),
            st.label
        ),
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
        new.iter().any(|n| {
            n.name == o.name
                && n.args.len() == o.args.len()
                && n.args
                    .iter()
                    .zip(o.args.iter())
                    .all(|(x, y)| x == y || *x == Value::Unknown || *y == Value::Unknown)
        })
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
            Scen::Quiet(t) => self.r.quiet(agent, *t),
            Scen::BelReal(x, cs) | Scen::BelImg(x, cs) => {
                if *x == agent {
                    vec![Scen::BelImg(*x, cs.clone())]
                } else {
                    vec![Scen::Skip]
                }
            }
            Scen::ForgetReal(x, slot) | Scen::SetImg(x, slot, _) => {
                if *x == agent {
                    self.r.world().slots[*slot]
                        .domain
                        .iter()
                        .map(|v| Scen::SetImg(*x, *slot, v.clone()))
                        .collect()
                } else {
                    vec![Scen::Skip]
                }
            }
            Scen::NestReal(x, y, cs) | Scen::NestImg(x, y, cs) => {
                if *x == agent {
                    vec![Scen::NestImg(*x, *y, cs.clone())]
                } else if *y == agent && matches!(s, Scen::NestImg(..)) {
                    vec![Scen::BelImg(*y, cs.clone())]
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
            Scen::Skip
            | Scen::Quiet(_)
            | Scen::BelReal(..)
            | Scen::NestReal(..)
            | Scen::NestImg(..)
            | Scen::ForgetReal(..)
            | Scen::SetImg(..) => Ok(true),
            Scen::BelImg(_, cs) => {
                for c in cs.iter() {
                    let ok = match c {
                        Constraint::Slot(slot, v) => m.vals[w as usize][*slot] == *v,
                        Constraint::F(Value::Formula(f)) => ev.truth(w, &f.env, &f.expr)?,
                        Constraint::F(_) | Constraint::Set(..) => true,
                    };
                    if !ok {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Scen::Ev(es) => {
                let world = self.r.world();
                if let Some(a) = es.unseen_by {
                    let views = self.r.observer_views(m, es, w)?;
                    if views[a as usize].is_some() {
                        return Ok(false); // they would have seen it
                    }
                }
                for act in &es.actions {
                    if es.ignore_needs || (es.lenient && self.r.said(act).is_some()) {
                        continue;
                    }
                    let info = world
                        .actions
                        .get(&*act.name)
                        .ok_or(format!("unknown action '{}'", act.name))?;
                    let env = self.r.action_env(act)?;
                    for n in &info.needs {
                        if es.revise && self.r.change_literals(m, w, &env, n).is_some() {
                            continue;
                        }
                        if !ev.truth(w, &env, n)? {
                            return Ok(false);
                        }
                    }
                }
                for f in &es.extra_pre {
                    if let Value::Formula(f) = f {
                        if es.revise && self.r.change_literals(m, w, &f.env, &f.expr).is_some() {
                            continue;
                        }
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
                if es.revise {
                    let world = self.r.world();
                    let mut sets = vec![];
                    for act in &es.actions {
                        if es.ignore_needs || (es.lenient && self.r.said(act).is_some()) {
                            continue;
                        }
                        let env = self.r.action_env(act)?;
                        for n in &world.actions[&*act.name].needs {
                            sets.extend(self.r.change_literals(m, w, &env, n).unwrap_or_default());
                        }
                    }
                    for f in &es.extra_pre {
                        if let Value::Formula(f) = f {
                            sets.extend(
                                self.r
                                    .change_literals(m, w, &f.env, &f.expr)
                                    .unwrap_or_default(),
                            );
                        }
                    }
                    for (slot, v) in sets {
                        cur[slot] = v;
                    }
                }
                for act in &es.actions {
                    self.r.apply_effects(m, w, act, &mut cur)?;
                }
                Ok(cur.into())
            }
            Scen::SetImg(_, slot, v) => {
                let mut cur: Vec<Value> = m.vals[w as usize].to_vec();
                cur[*slot] = v.clone();
                Ok(cur.into())
            }
            Scen::BelImg(_, cs) if cs.iter().any(|c| matches!(c, Constraint::Set(..))) => {
                let mut cur: Vec<Value> = m.vals[w as usize].to_vec();
                for c in cs.iter() {
                    if let Constraint::Set(slot, v) = c {
                        cur[*slot] = v.clone();
                    }
                }
                Ok(cur.into())
            }
            _ => Ok(m.vals[w as usize].clone()),
        }
    }
}
