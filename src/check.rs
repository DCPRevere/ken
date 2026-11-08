//! Checking a whole program: worlds in order, time travel, expectations.

use crate::ast::*;
use crate::engine::Runner;
use crate::eval::*;
use crate::kripke::Model;
use crate::state::*;
use crate::value::*;
use crate::world::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Engine {
    Auto,
    Explicit,
    Symbolic,
}

pub struct Checker<'a> {
    pub prog: &'a Program,
    pub engine: Engine,
    runs: RefCell<Vec<Option<Rc<Run>>>>,
    syms: RefCell<Vec<Option<crate::symbolic::Sym<'a>>>>,
    ded_cache: RefCell<HashMap<(usize, usize, u32), Rc<Model>>>,
}

pub struct Report {
    pub diags: Vec<Diag>,
    pub passed: usize,
    pub failed: usize,
}

impl<'a> Hub for Checker<'a> {
    fn snap(&self, world: usize, step: usize) -> Option<Snap> {
        self.runs.borrow().get(world)?.as_ref()?.snaps.get(step).cloned()
    }
    fn n_steps(&self, world: usize) -> Option<usize> {
        if let Some(Some(s)) = self.syms.borrow().get(world) {
            return Some(s.snaps.len());
        }
        Some(self.runs.borrow().get(world)?.as_ref()?.snaps.len())
    }
    fn deducible_model(&self, world: usize, step: usize, agent: u32) -> R<Rc<Model>> {
        if let Some(m) = self.ded_cache.borrow().get(&(world, step, agent)) {
            return Ok(m.clone());
        }
        let run = self.runs.borrow().get(world).and_then(|r| r.clone()).ok_or("world not checked yet")?;
        let mut dis: HashSet<CKey> = (*run.snaps[step].disabled).clone();
        for c in &run.conclusions {
            if c.agent == agent {
                dis.insert(c.key.clone());
            }
        }
        let r = Runner { prog: self.prog, wid: world, hub: self, seg_beliefs: run.seg_beliefs.clone(), suppress: None };
        let m = Rc::new(r.simulate(step, &dis, true)?);
        self.ded_cache.borrow_mut().insert((world, step, agent), m.clone());
        Ok(m)
    }
}

impl<'a> Checker<'a> {
    pub fn new(prog: &'a Program, engine: Engine) -> Self {
        Checker {
            prog,
            engine,
            runs: RefCell::new(vec![None; prog.worlds.len()]),
            syms: RefCell::new((0..prog.worlds.len()).map(|_| None).collect()),
            ded_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Try the symbolic engine; Ok(true) if it handled the world.
    fn try_symbolic(&self, wid: usize, diags: &mut Vec<Diag>) -> bool {
        use crate::symbolic::{Sym, SymErr};
        let w = &self.prog.worlds[wid];
        if self.engine == Engine::Explicit {
            return false;
        }
        match Sym::run(self.prog, wid, self) {
            Ok(mut sym) => {
                diags.append(&mut sym.diags);
                diags.push(Diag { level: Level::Note, line: 0, world: w.name.clone(), at: None, msg: format!("checked with the symbolic engine ({} BDD nodes)", sym.bdd.node_count()) });
                self.syms.borrow_mut()[wid] = Some(sym);
                true
            }
            Err(SymErr::Fallback(why)) => {
                if self.engine == Engine::Symbolic {
                    diags.push(Diag { level: Level::Error, line: 0, world: w.name.clone(), at: None, msg: format!("the symbolic engine can't check this world: {}", why) });
                    return true;
                }
                false
            }
            Err(SymErr::Error(m)) => {
                diags.push(Diag { level: Level::Error, line: 0, world: w.name.clone(), at: None, msg: m });
                true
            }
        }
    }

    pub fn check(&self) -> Report {
        let mut diags = vec![];
        let prog = self.prog;
        for wid in 0..prog.worlds.len() {
            let w = &prog.worlds[wid];
            for &o in &w.about {
                if o >= wid {
                    diags.push(Diag { level: Level::Error, line: 0, world: w.name.clone(), at: None, msg: format!("world {} must come after {}, which it is about", w.name, prog.worlds[o].name) });
                }
            }
            if self.try_symbolic(wid, &mut diags) {
                continue;
            }
            let same_world_segments = w.segments.iter().any(|s| s.origin_world == wid);
            let run = if same_world_segments {
                if prog.travel != Travel::Fixed {
                    diags.push(Diag { level: Level::Error, line: w.segments[0].span.line, world: w.name.clone(), at: None, msg: "a traveller arriving in their own world needs `time travel: fixed`".into() });
                }
                self.fixed_loop(wid, &mut diags)
            } else {
                let (beliefs, mut d) = self.segment_beliefs(wid, None);
                diags.append(&mut d);
                let r = Runner { prog, wid, hub: self, seg_beliefs: beliefs, suppress: None };
                r.run()
            };
            self.runs.borrow_mut()[wid] = Some(Rc::new(run));
            self.drift(wid, &mut diags);
        }
        let mut passed = 0;
        let mut failed = 0;
        for wid in 0..prog.worlds.len() {
            for e in &prog.worlds[wid].expects {
                self.expect(wid, e, &mut diags, &mut passed, &mut failed);
            }
        }
        if !prog.top_expects.is_empty() {
            match self.real_world() {
                Ok(wid) => {
                    for e in &prog.top_expects {
                        self.expect(wid, e, &mut diags, &mut passed, &mut failed);
                    }
                }
                Err(m) => diags.push(Diag { level: Level::Error, line: prog.top_expects[0].span.line, world: "-".into(), at: None, msg: m }),
            }
        }
        for r in self.runs.borrow().iter().flatten() {
            diags.extend(r.diags.iter().cloned());
        }
        // stable order: by world, then by line
        let order = |name: &str| prog.worlds.iter().position(|w| w.name == name).unwrap_or(usize::MAX);
        diags.sort_by_key(|d| (order(&d.world), d.line));
        Report { diags, passed, failed }
    }

    fn real_world(&self) -> Result<usize, String> {
        let prog = self.prog;
        if prog.worlds.len() == 1 {
            return Ok(0);
        }
        match prog.travel {
            Travel::Branching => Err("with `time travel: branching` every world is real, so put each `expect` inside its world".into()),
            _ => {
                let revised: HashSet<usize> = prog.worlds.iter().filter_map(|w| w.revises.as_ref().map(|r| r.0)).collect();
                let tips: Vec<usize> = (0..prog.worlds.len()).filter(|i| !revised.contains(i) && (prog.worlds[*i].revises.is_some() || revised.is_empty())).collect();
                if prog.worlds.iter().any(|w| w.revises.is_some()) {
                    if tips.len() != 1 {
                        return Err("with `time travel: overwrite` the revisions must form a single chain".into());
                    }
                    Ok(tips[0])
                } else {
                    Err("this file has several worlds; put each `expect` inside the world it is about".into())
                }
            }
        }
    }

    /// Beliefs a segment brings: the origin agent's beliefs about unchanging facts.
    fn segment_beliefs(&self, wid: usize, own: Option<&Run>) -> (HashMap<u32, Vec<(usize, Value)>>, Vec<Diag>) {
        let prog = self.prog;
        let w = &prog.worlds[wid];
        let mut out = HashMap::new();
        let mut diags = vec![];
        for s in &w.segments {
            let run_rc;
            let run: &Run = if s.origin_world == wid {
                match own {
                    Some(r) => r,
                    None => {
                        out.insert(s.agent, vec![]);
                        continue;
                    }
                }
            } else {
                match self.runs.borrow().get(s.origin_world).and_then(|r| r.clone()) {
                    Some(r) => {
                        run_rc = r;
                        &run_rc
                    }
                    None => {
                        diags.push(Diag { level: Level::Error, line: s.span.line, world: w.name.clone(), at: None, msg: "the traveller's original world must come first".into() });
                        continue;
                    }
                }
            };
            match self.project(run, s.origin_world, &s.origin_agent, &s.at, wid) {
                Ok(b) => {
                    out.insert(s.agent, b);
                }
                Err(m) => diags.push(Diag { level: Level::Error, line: s.span.line, world: w.name.clone(), at: None, msg: m }),
            }
        }
        (out, diags)
    }

    fn project(&self, run: &Run, ow: usize, agent: &str, at: &TimeRef, tw: usize) -> Result<Vec<(usize, Value)>, String> {
        let prog = self.prog;
        let o = &prog.worlds[ow];
        let t = &prog.worlds[tw];
        let a = *o.agent_names.get(agent).ok_or(format!("world {} has no agent '{}'", o.name, agent))?;
        let step = match at {
            TimeRef::Event { label, .. } => *o.label_index.get(label).ok_or(format!("world {} has no event '{}'", o.name, label))?,
            TimeRef::Start => 0,
            _ => o.steps.len() - 1,
        };
        let snap = run.snaps.get(step).ok_or("the traveller's departure was never reached")?;
        let m = &snap.model;
        let mut out = vec![];
        let mut slots: Vec<usize> = o.relevant.iter().copied().collect();
        slots.sort_unstable();
        for s in slots {
            let sl = &o.slots[s];
            if o.changeable.contains(&sl.fact) {
                continue;
            }
            let succ = m.succ(a, m.actual);
            if succ.is_empty() {
                continue;
            }
            let v0 = &m.vals[succ[0] as usize][s];
            if succ.iter().all(|v| &m.vals[*v as usize][s] == v0) {
                // map the slot into the target world by names
                let args: Option<Vec<Value>> = sl
                    .args
                    .iter()
                    .map(|x| match x {
                        Value::Agent(_, i) => t.agent_names.get(&o.agents[*i as usize].name).map(|j| Value::Agent(tw as u16, *j)),
                        other => Some(other.clone()),
                    })
                    .collect();
                if let Some(args) = args {
                    if let Some(ts) = t.slot_of.get(&(sl.fact.clone(), args)) {
                        out.push((*ts, v0.clone()));
                    }
                }
            }
        }
        Ok(out)
    }

    /// `time travel: fixed`: iterate to a self-consistent loop, then check that
    /// what the traveller knows has an origin outside the loop.
    fn fixed_loop(&self, wid: usize, diags: &mut Vec<Diag>) -> Run {
        let prog = self.prog;
        let w = &prog.worlds[wid];
        // grounded knowledge: run with the travellers' own actions suppressed
        let mut grounded: HashMap<u32, Vec<(usize, Value)>> = HashMap::new();
        for s in w.segments.iter().filter(|s| s.origin_world == wid) {
            let r = Runner { prog, wid, hub: self, seg_beliefs: HashMap::new(), suppress: Some(s.agent) };
            let run = r.run();
            let b = self.project(&run, wid, &s.origin_agent, &s.at, wid).unwrap_or_default();
            grounded.insert(s.agent, b);
        }
        let mut beliefs = grounded.clone();
        let mut last: Option<Run> = None;
        for _ in 0..8 {
            let r = Runner { prog, wid, hub: self, seg_beliefs: beliefs.clone(), suppress: None };
            let run = r.run();
            let (next, _) = self.segment_beliefs(wid, Some(&run));
            let settled = next == beliefs;
            beliefs = next;
            last = Some(run);
            if settled {
                break;
            }
        }
        let run = last.unwrap();
        let (fin, _) = self.segment_beliefs(wid, Some(&run));
        if fin != run.seg_beliefs {
            diags.push(Diag { level: Level::Error, line: w.segments[0].span.line, world: w.name.clone(), at: None, msg: "the time loop never settles: what the traveller brings back keeps changing".into() });
        }
        for s in w.segments.iter().filter(|s| s.origin_world == wid) {
            let g = grounded.get(&s.agent).cloned().unwrap_or_default();
            let f = run.seg_beliefs.get(&s.agent).cloned().unwrap_or_default();
            let orphan: Vec<String> = f
                .iter()
                .filter(|x| !g.contains(x))
                .map(|(slot, v)| {
                    let sl = &w.slots[*slot];
                    let name = if sl.args.is_empty() { sl.fact.clone() } else { format!("{}({})", sl.fact, sl.args.iter().map(|a| prog.show(a)).collect::<Vec<_>>().join(", ")) };
                    format!("{} = {}", name, prog.show(v))
                })
                .collect();
            if !orphan.is_empty() && !prog.allow_bootstrap {
                diags.push(Diag {
                    level: Level::Error,
                    line: s.span.line,
                    world: w.name.clone(),
                    at: None,
                    msg: format!(
                        "bootstrap paradox: {} knows `{}` only because of the loop; nothing outside it is the origin. Add `allow bootstrap`, or let someone actually observe it",
                        w.agents[s.agent as usize].name,
                        orphan.join("`, `")
                    ),
                });
            }
        }
        run
    }

    /// Warn when a traveller remembers events that the revised world no longer contains.
    fn drift(&self, wid: usize, diags: &mut Vec<Diag>) {
        let prog = self.prog;
        let w = &prog.worlds[wid];
        let Some((base, from)) = &w.revises else { return };
        let runs = self.runs.borrow();
        let Some(Some(cur)) = runs.get(wid) else { return };
        for s in &w.segments {
            if s.origin_world == wid {
                continue;
            }
            let o = &prog.worlds[s.origin_world];
            let Some(Some(orun)) = runs.get(s.origin_world) else { continue };
            let Some(&oa) = o.agent_names.get(&s.origin_agent) else { continue };
            let step = match &s.at {
                TimeRef::Event { label, .. } => o.label_index.get(label).copied().unwrap_or(0),
                _ => 0,
            };
            let from_ix = if s.origin_world == *base { prog.worlds[*base].label_index.get(from).copied().unwrap_or(0) } else { 0 };
            let Some(snap) = orun.snaps.get(step) else { continue };
            let mut mems: Vec<(&String, &ViewRec)> = snap.registry.views[oa as usize].iter().filter(|(_, v)| v.step > from_ix).collect();
            mems.sort_by_key(|(_, v)| v.step);
            for (label, v) in mems {
                let mapped: Vec<ActionInst> = v
                    .actions
                    .iter()
                    .map(|a| ActionInst {
                        name: a.name.clone(),
                        args: a
                            .args
                            .iter()
                            .map(|x| match x {
                                Value::Agent(aw, i) if *aw as usize == s.origin_world => w.agent_names.get(&o.agents[*i as usize].name).map(|j| Value::Agent(wid as u16, *j)).unwrap_or(x.clone()),
                                other => other.clone(),
                            })
                            .collect(),
                    })
                    .collect();
                let happens = cur.snaps.iter().any(|sn| crate::engine::contains(&sn.actual, &mapped));
                if !happens {
                    diags.push(Diag {
                        level: Level::Warning,
                        line: s.span.line,
                        world: w.name.clone(),
                        at: None,
                        msg: format!(
                            "memory drift: {} remembers `{}` ({}.{}), which never happens in {}",
                            w.agents[s.agent as usize].name,
                            prog.show_actions(&v.actions),
                            o.name,
                            label,
                            w.name
                        ),
                    });
                }
            }
        }
    }

    fn expect(&self, wid: usize, e: &Expect, diags: &mut Vec<Diag>, passed: &mut usize, failed: &mut usize) {
        let prog = self.prog;
        let wname = prog.worlds[wid].name.clone();
        let steps: Result<Vec<usize>, String> = (|| {
            Ok(match &e.time {
                ExpectTime::At(t) => vec![self.local_time(wid, t)?],
                ExpectTime::Before(t) => {
                    let s = self.local_time(wid, t)?;
                    if s == 0 {
                        return Err("nothing comes before start".into());
                    }
                    vec![s - 1]
                }
                ExpectTime::Throughout(a, b) => {
                    let (x, y) = (self.local_time(wid, a)?, self.local_time(wid, b)?);
                    (x..=y).collect()
                }
            })
        })();
        let steps = match steps {
            Ok(s) => s,
            Err(m) => {
                diags.push(Diag { level: Level::Error, line: e.span.line, world: wname, at: None, msg: m });
                return;
            }
        };
        if self.syms.borrow()[wid].is_some() {
            self.expect_symbolic(wid, e, &steps, diags, passed, failed);
            return;
        }
        let n = self.n_steps(wid).unwrap_or(0);
        for f in &e.formulas {
            let mut ok = true;
            for &s in &steps {
                if s >= n {
                    diags.push(Diag { level: Level::Warning, line: f.span.line, world: wname.clone(), at: Some(prog.worlds[wid].steps[s].label.clone()), msg: format!("not checked (this point was never reached): `{}`", prog.text(f.span)) });
                    ok = false;
                    break;
                }
                let snap = self.snap(wid, s).unwrap();
                let ev = Ev { prog, wid, model: &snap.model, step: s, registry: Some(&snap.registry), foreign: Some(&snap.foreign), hub: Some(self), vals: None };
                let label = prog.worlds[wid].steps[s].label.clone();
                match ev.strict_truth(snap.model.actual, &vec![], f) {
                    Ok(Some(true)) => {}
                    Ok(Some(false)) => {
                        diags.push(Diag { level: Level::Error, line: f.span.line, world: wname.clone(), at: Some(label), msg: format!("expected `{}`, but it is false", prog.text(f.span)) });
                        ok = false;
                        break;
                    }
                    Ok(None) => {
                        diags.push(Diag { level: Level::Warning, line: f.span.line, world: wname.clone(), at: Some(label), msg: format!("can't decide `{}`", prog.text(f.span)) });
                        ok = false;
                        break;
                    }
                    Err(m) => {
                        diags.push(Diag { level: Level::Error, line: f.span.line, world: wname.clone(), at: Some(label), msg: m });
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                *passed += 1;
            } else {
                *failed += 1;
            }
        }
    }

    fn expect_symbolic(&self, wid: usize, e: &Expect, steps: &[usize], diags: &mut Vec<Diag>, passed: &mut usize, failed: &mut usize) {
        use crate::symbolic::SymErr;
        let prog = self.prog;
        let wname = prog.worlds[wid].name.clone();
        let mut syms = self.syms.borrow_mut();
        let sym = syms[wid].as_mut().unwrap();
        for f in &e.formulas {
            let mut ok = true;
            for &s in steps {
                let label = prog.worlds[wid].steps[s].label.clone();
                if s >= sym.snaps.len() {
                    ok = false;
                    break;
                }
                match sym.eval_at(s, f) {
                    Ok(true) => {}
                    Ok(false) => {
                        diags.push(Diag { level: Level::Error, line: f.span.line, world: wname.clone(), at: Some(label), msg: format!("expected `{}`, but it is false", prog.text(f.span)) });
                        ok = false;
                        break;
                    }
                    Err(SymErr::Fallback(why)) => {
                        diags.push(Diag { level: Level::Error, line: f.span.line, world: wname.clone(), at: Some(label), msg: format!("the symbolic engine can't evaluate `{}` ({}); try --engine explicit", prog.text(f.span), why) });
                        ok = false;
                        break;
                    }
                    Err(SymErr::Error(m)) => {
                        diags.push(Diag { level: Level::Error, line: f.span.line, world: wname.clone(), at: Some(label), msg: m });
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                *passed += 1;
            } else {
                *failed += 1;
            }
        }
    }

    fn local_time(&self, wid: usize, t: &TimeRef) -> Result<usize, String> {
        let (w, s) = resolve_time(self.prog, wid, t, self, &self.prog.params)?;
        if w != wid {
            return Err("an `expect` can only name times in its own world; use `(…) at <event>` inside the formula".into());
        }
        Ok(s)
    }
}
