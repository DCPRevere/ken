//! Questions you can ask a checked story: why, who, what if, suggest, and a timeline.

use crate::ast::*;
use crate::check::{Checker, Engine, Report};
use crate::state::{CKey, Diag, Level};
use crate::value::Value;
use crate::world::Program;
use std::collections::HashSet;
use std::rc::Rc;

/// Find a world and step by label: `e3`, `Tale.e3`, `start` or `end`.
pub fn find_step(prog: &Program, spec: &str) -> Result<(usize, usize), String> {
    let (world, label) = match spec.split_once('.') {
        Some((w, l)) => (Some(w), l),
        None => (None, spec),
    };
    for (wid, w) in prog.worlds.iter().enumerate() {
        if let Some(wn) = world {
            if w.name != wn {
                continue;
            }
        }
        if label == "end" {
            return Ok((wid, w.steps.len() - 1));
        }
        if let Some(&s) = w.label_index.get(label) {
            return Ok((wid, s));
        }
    }
    Err(format!("no event '{}'", spec))
}

fn mk(kind: ExprKind, span: Span) -> E {
    Rc::new(Expr { kind, span })
}

fn agent_expr(name: &str, span: Span) -> E {
    mk(ExprKind::Name(name.to_string()), span)
}

// ------------------------------------------------------------------ why

/// Why does an agent believe (or know, or suspect) something at a step? Each source
/// is tested by taking it away and running the world again.
pub fn why(
    prog: &Program,
    checker: &Checker,
    wid: usize,
    step: usize,
    f: &E,
) -> Result<String, String> {
    let w = &prog.worlds[wid];
    let label = &w.steps[step].label;
    let ftext = prog.text(f.span).to_string();
    match checker.eval_formula(wid, step, f)? {
        Some(true) => {}
        Some(false) => {
            return Ok(format!(
                "`{}` is false at {}, so there's nothing to explain. Try `ken who`.\n",
                ftext, label
            ))
        }
        None => return Ok(format!("Ken can't decide `{}` at {}.\n", ftext, label)),
    }
    let agent_e = match &f.kind {
        ExprKind::Epistemic { agent, .. } | ExprKind::Suspects { agent, .. } => agent.clone(),
        _ => return Ok(format!("`{}` is true at {}. `ken why` explains beliefs: ask about `X believes …`, `X knows …` or `X suspects …`.\n", ftext, label)),
    };
    let a = match w.agent_names.get(prog.text(agent_e.span)) {
        Some(a) => *a,
        None => {
            return Err(format!(
                "'{}' is not an agent of world {}",
                prog.text(agent_e.span),
                w.name
            ))
        }
    };
    let run = checker
        .run_of(wid)
        .ok_or("that world wasn't checked (the symbolic engine has no history to explain)")?;
    let snap = run.snaps.get(step).ok_or("that point was never reached")?;
    // sources: events the agent saw directly, and their own conclusions so far
    let mut seen: Vec<(usize, String)> = snap.registry.views[a as usize]
        .iter()
        .filter(|(_, v)| v.direct && v.step <= step && v.step > 0)
        .map(|(l, v)| (v.step, l.clone()))
        .collect();
    seen.sort();
    let concls: Vec<_> = run
        .conclusions
        .iter()
        .filter(|c| {
            c.agent == a && c.step <= step && !snap.disabled.contains(&c.key) && c.foreign.is_none()
        })
        .cloned()
        .collect();
    let holds_without = |blind: HashSet<(u32, usize)>, dis: HashSet<CKey>| -> Option<bool> {
        let r = checker.rerun(wid, blind, dis);
        checker.eval_in(wid, &r, step, f).ok().flatten()
    };
    let mut out = format!("{} at {}, because of:\n", ftext, label);
    let mut needed = 0;
    for (s, l) in &seen {
        let what = prog.show_actions(&snap.registry.views[a as usize][l].actions).split_whitespace().collect::<Vec<_>>().join(" ");
        let h = holds_without([(a, *s)].into_iter().collect(), HashSet::new());
        let mark = match h {
            Some(false) => {
                needed += 1;
                "needed"
            }
            Some(true) => "not needed on its own",
            None => "can't tell",
        };
        out.push_str(&format!(
            "  {:<8} {} saw {}  ({}, line {})\n",
            l, w.agents[a as usize].name, what, mark, w.steps[*s].span.line
        ));
    }
    for c in &concls {
        let h = holds_without(HashSet::new(), [c.key.clone()].into_iter().collect());
        let mark = match h {
            Some(false) => {
                needed += 1;
                "needed"
            }
            Some(true) => "not needed on its own",
            None => "can't tell",
        };
        out.push_str(&format!(
            "  {:<8} they concluded `{}`  ({}, line {})\n",
            w.steps[c.step].label,
            prog.show(&c.formula),
            mark,
            c.line
        ));
    }
    if seen.is_empty() && concls.is_empty() {
        out.push_str(
            "  nothing they saw or concluded: it comes from how things stood at the start\n",
        );
        return Ok(out);
    }
    let all_blind: HashSet<(u32, usize)> = seen.iter().map(|(s, _)| (a, *s)).collect();
    let all_dis: HashSet<CKey> = concls.iter().map(|c| c.key.clone()).collect();
    if holds_without(all_blind, all_dis) == Some(true) {
        out.push_str(
            "  It still holds without all of these: it comes from how things stood at the start.\n",
        );
    } else if needed == 0 {
        out.push_str("  No single source is needed: several of them each lead there.\n");
    }
    out.push_str("(\"needed\": take it away and the belief goes.)\n");
    Ok(out)
}

// ------------------------------------------------------------------ who

/// Who knows, believes, or could work out a formula at a step?
pub fn who(
    prog: &Program,
    checker: &Checker,
    wid: usize,
    step: usize,
    f: &E,
) -> Result<String, String> {
    let w = &prog.worlds[wid];
    let label = &w.steps[step].label;
    let ftext = prog.text(f.span).to_string();
    let truth = checker.eval_formula(wid, step, f);
    let mut out = match &truth {
        Ok(Some(t)) => format!("At {}, `{}` is {}.\n", label, ftext, t),
        _ => format!("At {}, `{}`:\n", label, ftext),
    };
    let not_f = mk(ExprKind::Not(f.clone()), f.span);
    let width = w.agents.iter().map(|a| a.name.len()).max().unwrap_or(4);
    for ag in &w.agents {
        let ae = agent_expr(&ag.name, f.span);
        let bel = mk(
            ExprKind::Epistemic {
                agent: ae.clone(),
                mode: KMode::Believes,
                body: f.clone(),
            },
            f.span,
        );
        let bel_not = mk(
            ExprKind::Epistemic {
                agent: ae.clone(),
                mode: KMode::Believes,
                body: not_f.clone(),
            },
            f.span,
        );
        let ded = mk(
            ExprKind::Deducible {
                agent: ae.clone(),
                body: f.clone(),
            },
            f.span,
        );
        if let Some(tw) = ag.sees_all_of {
            out.push_str(&format!(
                "  {:<width$}  sees everything in {}\n",
                ag.name,
                prog.worlds[tw].name,
                width = width
            ));
            continue;
        }
        let b = checker.eval_formula(wid, step, &bel).ok().flatten();
        let bn = checker.eval_formula(wid, step, &bel_not).ok().flatten();
        let t = truth.clone().ok().flatten();
        let status = match (b, bn, t) {
            (Some(true), Some(true), _) => "has contradictory beliefs".to_string(),
            (Some(true), _, Some(true)) => "knows it".to_string(),
            (Some(true), _, Some(false)) => "believes it, wrongly".to_string(),
            (Some(true), _, None) => "believes it".to_string(),
            (_, Some(true), Some(false)) => "knows it's false".to_string(),
            (_, Some(true), Some(true)) => "believes the opposite, wrongly".to_string(),
            (_, Some(true), None) => "believes the opposite".to_string(),
            _ => match checker.eval_formula(wid, step, &ded).ok().flatten() {
                Some(true) => {
                    "doesn't believe it yet, but could work it out from what they've seen"
                        .to_string()
                }
                _ => "doesn't know".to_string(),
            },
        };
        out.push_str(&format!(
            "  {:<width$}  {}\n",
            ag.name,
            status,
            width = width
        ));
    }
    Ok(out)
}

// ------------------------------------------------------------------ what if

/// The lines of a timeline event: its own line and the indented lines under it.
fn event_block(lines: &[String], spec: &str) -> Option<(usize, usize, usize)> {
    // `World.label` searches only inside that world
    let (range, label) = match spec.split_once('.') {
        Some((w, l)) => {
            let start = lines.iter().position(|x| x.trim_start() == format!("world {}", w) || x.starts_with(&format!("world {} ", w)))?;
            let end = lines.iter().enumerate().skip(start + 1).find(|(_, x)| x.starts_with("world ")).map(|(i, _)| i).unwrap_or(lines.len());
            (start..end, l)
        }
        None => (0..lines.len(), spec),
    };
    for i in range {
        let l = &lines[i];
        let t = l.trim_start();
        let ind = l.len() - t.len();
        if ind == 0 {
            continue;
        }
        let head = t
            .split(|c: char| c == ':' || c == ' ' || c == '@')
            .next()
            .unwrap_or("");
        if head == label
            && (t[label.len()..].trim_start().starts_with(':')
                || t[label.len()..].trim_start().starts_with('@'))
        {
            let mut j = i + 1;
            while j < lines.len() {
                let lt = lines[j].trim_start();
                let li = lines[j].len() - lt.len();
                if lt.is_empty() || lt.starts_with('#') || li > ind {
                    j += 1;
                } else {
                    break;
                }
            }
            while j > i + 1 && lines[j - 1].trim().is_empty() {
                j -= 1;
            }
            return Some((i, j, ind));
        }
    }
    None
}

pub enum Change {
    Drop(String),
    Move(String, String),
}

pub fn apply_change(src: &str, change: &Change) -> Result<String, String> {
    let mut lines: Vec<String> = src.lines().map(|s| s.to_string()).collect();
    match change {
        Change::Drop(l) => {
            let (a, b, _) =
                event_block(&lines, l).ok_or(format!("no event '{}' in the timeline", l))?;
            lines.drain(a..b);
        }
        Change::Move(l, after) => {
            let (a, b, _) =
                event_block(&lines, l).ok_or(format!("no event '{}' in the timeline", l))?;
            let block: Vec<String> = lines.drain(a..b).collect();
            let (_, e, _) = event_block(&lines, after)
                .ok_or(format!("no event '{}' in the timeline", after))?;
            for (k, x) in block.into_iter().enumerate() {
                lines.insert(e + k, x);
            }
        }
    }
    Ok(lines.join("\n") + "\n")
}

fn diag_key(d: &Diag) -> (u8, String, String, String) {
    let lv = match d.level {
        Level::Error => 0,
        Level::Warning => 1,
        Level::Note => 2,
    };
    (
        lv,
        d.world.clone(),
        d.at.clone().unwrap_or_default(),
        d.msg.clone(),
    )
}

fn show_diag(d: &Diag) -> String {
    let tag = match d.level {
        Level::Error => "error",
        Level::Warning => "warning",
        Level::Note => "note",
    };
    let w = if d.world == "main" {
        String::new()
    } else {
        format!("{} ", d.world)
    };
    match &d.at {
        Some(at) => format!("{} [{}@ {}]: {}", tag, w, at, d.msg),
        None if w.is_empty() => format!("{}: {}", tag, d.msg),
        None => format!("{} [{}]: {}", tag, d.world, d.msg),
    }
}

fn summary(r: &Report) -> String {
    let errors = r.diags.iter().filter(|d| d.level == Level::Error).count();
    format!(
        "{} hold, {} failed, {} error(s)",
        r.passed, r.failed, errors
    )
}

type Loader<'l> = &'l dyn Fn(&str) -> Result<Program, String>;

fn check_src(load: Loader, src: &str, engine: Engine) -> Result<Report, String> {
    let prog = load(src)?;
    let c = Checker::new(&prog, engine);
    Ok(c.check())
}

pub fn whatif(load: Loader, src: &str, engine: Engine, change: &Change) -> Result<String, String> {
    let before = check_src(load, src, engine)?;
    let new_src = apply_change(src, change)?;
    let after = check_src(load, &new_src, engine)
        .map_err(|e| format!("after the change the story no longer loads: {}", e))?;
    let bk: HashSet<_> = before
        .diags
        .iter()
        .filter(|d| d.level != Level::Note || d.msg.contains("no longer"))
        .map(diag_key)
        .collect();
    let ak: HashSet<_> = after
        .diags
        .iter()
        .filter(|d| d.level != Level::Note || d.msg.contains("no longer"))
        .map(diag_key)
        .collect();
    let mut out = match change {
        Change::Drop(l) => format!("What if {} never happened?\n", l),
        Change::Move(l, a) => format!("What if {} happened after {}?\n", l, a),
    };
    let mut any = false;
    for d in &before.diags {
        if !ak.contains(&diag_key(d)) && bk.contains(&diag_key(d)) {
            out.push_str(&format!("  - {}\n", show_diag(d)));
            any = true;
        }
    }
    for d in &after.diags {
        if !bk.contains(&diag_key(d)) && ak.contains(&diag_key(d)) {
            out.push_str(&format!("  + {}\n", show_diag(d)));
            any = true;
        }
    }
    if !any {
        out.push_str("  nothing changes in what Ken reports\n");
    }
    out.push_str(&format!(
        "Before: {}. After: {}.\n",
        summary(&before),
        summary(&after)
    ));
    Ok(out)
}

// ------------------------------------------------------------------ suggest

/// Fact-level parts of a formula that someone could be told.
fn tellable(e: &E, out: &mut Vec<E>) {
    match &e.kind {
        ExprKind::Epistemic { body, .. }
        | ExprKind::Deducible { body, .. }
        | ExprKind::Possible { body, .. }
        | ExprKind::Suspects { body, .. } => {
            if is_plain(body) {
                out.push(body.clone());
            } else {
                tellable(body, out);
            }
        }
        ExprKind::Not(x) => tellable(x, out),
        ExprKind::Bin(_, a, b) => {
            tellable(a, out);
            tellable(b, out);
        }
        ExprKind::At(x, _) => tellable(x, out),
        _ => {}
    }
}

fn is_plain(e: &E) -> bool {
    match &e.kind {
        ExprKind::Epistemic { .. }
        | ExprKind::Common { .. }
        | ExprKind::Deducible { .. }
        | ExprKind::Possible { .. }
        | ExprKind::Saw { .. }
        | ExprKind::At(..)
        | ExprKind::Wants { .. }
        | ExprKind::Suspects { .. } => false,
        ExprKind::Not(x) | ExprKind::Neg(x) => is_plain(x),
        ExprKind::Bin(_, a, b) => is_plain(a) && is_plain(b),
        ExprKind::Quant { body, .. } => is_plain(body),
        _ => true,
    }
}

/// For each failing expectation, look for one event that, added just before, makes it
/// hold without new errors.
pub fn suggest(load: Loader, src: &str, engine: Engine, max: usize) -> Result<String, String> {
    let prog = load(src)?;
    let checker = Checker::new(&prog, engine);
    let report = checker.check();
    let errors_before = report
        .diags
        .iter()
        .filter(|d| d.level == Level::Error)
        .count();
    let failing: Vec<&Diag> = report
        .diags
        .iter()
        .filter(|d| d.level == Level::Error && d.msg.starts_with("expected `"))
        .collect();
    if failing.is_empty() {
        return Ok("Every expectation holds; nothing to suggest.\n".into());
    }
    let mut out = String::new();
    for d in failing {
        let text = d
            .msg
            .trim_start_matches("expected `")
            .split("`, but")
            .next()
            .unwrap_or("")
            .to_string();
        let at = d.at.clone().unwrap_or_default();
        out.push_str(&format!("To make `{}` hold at {}:\n", text, at));
        let Some(wid) = prog.world_by_name(&d.world).or(if prog.worlds.len() == 1 {
            Some(0)
        } else {
            None
        }) else {
            continue;
        };
        let w = &prog.worlds[wid];
        let Some(&step) = w.label_index.get(&at) else {
            continue;
        };
        if step == 0 {
            out.push_str("  (it's about the start; change what is seen at the start instead)\n");
            continue;
        }
        // the expectation's formula, to find what could be told
        let mut tells: Vec<String> = vec![];
        let mut targets: Vec<String> = vec![];
        for e in w
            .expects
            .iter()
            .chain(prog.top_expects.iter())
            .flat_map(|x| x.formulas.iter())
        {
            if prog.text(e.span) == text {
                let mut parts = vec![];
                tellable(e, &mut parts);
                for p in parts {
                    tells.push(prog.text(p.span).to_string());
                }
                collect_agents(&prog, wid, e, &mut targets);
            }
        }
        let mut cands: Vec<String> = vec![];
        let people: Vec<&str> = w.agents.iter().map(|a| a.name.as_str()).collect();
        for t in &tells {
            for y in &targets {
                for x in &people {
                    if x != y {
                        cands.push(format!("tell({}, {}, {})", x, y, t));
                    }
                }
            }
            for x in &people {
                cands.push(format!("announce({}, {})", x, t));
            }
        }
        let mut names: Vec<&String> = w
            .actions
            .keys()
            .filter(|n| n.as_str() != "tell" && n.as_str() != "announce")
            .collect();
        names.sort();
        for n in names {
            let info = &w.actions[n];
            let mut combos: Vec<Vec<String>> = vec![vec![]];
            let mut finite = true;
            for (_, ty) in &info.params {
                let Some(dom) = crate::world::domain_of(w, ty) else {
                    finite = false;
                    break;
                };
                let mut next = vec![];
                for c in &combos {
                    for v in &dom {
                        let mut c2 = c.clone();
                        c2.push(prog.show(v));
                        next.push(c2);
                    }
                }
                combos = next;
            }
            if finite {
                for c in combos {
                    cands.push(format!("{}({})", n, c.join(", ")));
                }
            }
        }
        cands.truncate(400);
        let lines: Vec<String> = src.lines().map(|s| s.to_string()).collect();
        let Some((line_ix, _, ind)) = event_block(&lines, &at) else {
            continue;
        };
        let mut found: Vec<(usize, String)> = vec![];
        for c in &cands {
            let mut l2 = lines.clone();
            l2.insert(line_ix, format!("{}suggested: {}", " ".repeat(ind), c));
            let s2 = l2.join("\n") + "\n";
            let Ok(r) = check_src(load, &s2, engine) else {
                continue;
            };
            let still = r
                .diags
                .iter()
                .any(|x| x.level == Level::Error && x.msg == d.msg && x.world == d.world);
            let errs = r.diags.iter().filter(|x| x.level == Level::Error).count();
            if !still && errs < errors_before {
                let noise = r.diags.len();
                found.push((noise, c.clone()));
            }
        }
        found.sort();
        if found.is_empty() {
            out.push_str("  no single added event does it\n");
        }
        for (_, c) in found.iter().take(max) {
            out.push_str(&format!("  before {}:  {}\n", at, c));
        }
    }
    Ok(out)
}

fn collect_agents(prog: &Program, wid: usize, e: &E, out: &mut Vec<String>) {
    let w = &prog.worlds[wid];
    match &e.kind {
        ExprKind::Epistemic { agent, body, .. }
        | ExprKind::Deducible { agent, body }
        | ExprKind::Possible { agent, body }
        | ExprKind::Suspects { agent, body } => {
            let n = prog.text(agent.span).to_string();
            if w.agent_names.contains_key(&n) && !out.contains(&n) {
                out.push(n);
            }
            collect_agents(prog, wid, body, out);
        }
        ExprKind::Not(x) | ExprKind::At(x, _) => collect_agents(prog, wid, x, out),
        ExprKind::Bin(_, a, b) => {
            collect_agents(prog, wid, a, out);
            collect_agents(prog, wid, b, out);
        }
        _ => {}
    }
}

// ------------------------------------------------------------------ timeline

/// One cell: what an agent believes about a fact at a step.
#[derive(Clone)]
pub struct Cell {
    pub text: String,
    pub kind: CellKind,
}

#[derive(Clone, Copy, PartialEq)]
pub enum CellKind {
    Truth,
    Right,
    Wrong,
    Unsure,
    Broken,
}

pub struct Grid {
    pub world: String,
    pub fact: String,
    pub steps: Vec<String>,
    pub rows: Vec<(String, Vec<Cell>)>,
}

/// For each world and fact: the truth and each agent's belief at every step.
pub fn timeline(prog: &Program, checker: &Checker, only: Option<usize>) -> Vec<Grid> {
    let mut grids = vec![];
    for (wid, w) in prog.worlds.iter().enumerate() {
        if only.is_some() && only != Some(wid) {
            continue;
        }
        let Some(run) = checker.run_of(wid) else {
            continue;
        };
        let steps: Vec<String> = run
            .snaps
            .iter()
            .enumerate()
            .map(|(i, _)| w.steps[i].label.clone())
            .collect();
        let mut slots: Vec<usize> = w.relevant.iter().copied().collect();
        slots.sort_by_key(|s| slot_name(prog, wid, *s));
        for slot in slots {
            let truth: Vec<Value> = run
                .snaps
                .iter()
                .map(|s| s.model.vals[s.model.actual as usize][slot].clone())
                .collect();
            if w.slots[slot].fact == "honest" && truth.iter().all(|v| *v == Value::Bool(true)) {
                continue;
            }
            let mut rows = vec![(
                "truth".to_string(),
                truth
                    .iter()
                    .map(|v| Cell {
                        text: prog.show(v),
                        kind: CellKind::Truth,
                    })
                    .collect(),
            )];
            for (a, ag) in w.agents.iter().enumerate() {
                let mut cells = vec![];
                for (i, s) in run.snaps.iter().enumerate() {
                    let m = &s.model;
                    let succ = m.succ(a as u32, m.actual);
                    let cell = if succ.is_empty() {
                        Cell {
                            text: "⊥".into(),
                            kind: CellKind::Broken,
                        }
                    } else {
                        let v0 = &m.vals[succ[0] as usize][slot];
                        if succ.iter().all(|v| &m.vals[*v as usize][slot] == v0) {
                            Cell {
                                text: prog.show(v0),
                                kind: if *v0 == truth[i] {
                                    CellKind::Right
                                } else {
                                    CellKind::Wrong
                                },
                            }
                        } else {
                            Cell {
                                text: "?".into(),
                                kind: CellKind::Unsure,
                            }
                        }
                    };
                    cells.push(cell);
                }
                rows.push((ag.name.clone(), cells));
            }
            grids.push(Grid {
                world: w.name.clone(),
                fact: slot_name(prog, wid, slot),
                steps: steps.clone(),
                rows,
            });
        }
        // a reader's beliefs about another world
        for &tw in &w.about {
            let Some(trun) = checker.run_of(tw) else {
                continue;
            };
            let tlast = trun
                .snaps
                .last()
                .map(|s| s.model.vals[s.model.actual as usize].to_vec())
                .unwrap_or_default();
            let tworld = &prog.worlds[tw];
            let mut slots: Vec<usize> = tworld
                .relevant
                .iter()
                .copied()
                .filter(|s| tworld.slots[*s].fact != "honest")
                .collect();
            slots.sort_by_key(|s| slot_name(prog, tw, *s));
            for slot in slots {
                let mut rows = vec![];
                for (a, ag) in w.agents.iter().enumerate() {
                    if ag.sees_all_of == Some(tw) {
                        continue;
                    }
                    let cells: Vec<Cell> = run
                        .snaps
                        .iter()
                        .map(|s| {
                            let st = s.foreign.get(&(a as u32, tw)).cloned().unwrap_or_default();
                            let k = crate::foreign::with_conclusions(prog, tw, &st);
                            match k.get(&slot) {
                                Some(v) => Cell {
                                    text: prog.show(v),
                                    kind: if Some(v) == tlast.get(slot) {
                                        CellKind::Right
                                    } else {
                                        CellKind::Wrong
                                    },
                                },
                                None => Cell {
                                    text: "?".into(),
                                    kind: CellKind::Unsure,
                                },
                            }
                        })
                        .collect();
                    rows.push((ag.name.clone(), cells));
                }
                if rows.is_empty() {
                    continue;
                }
                rows.insert(
                    0,
                    (
                        "truth (at the end)".into(),
                        steps
                            .iter()
                            .map(|_| Cell {
                                text: tlast.get(slot).map(|v| prog.show(v)).unwrap_or("?".into()),
                                kind: CellKind::Truth,
                            })
                            .collect(),
                    ),
                );
                grids.push(Grid {
                    world: format!("{} (about {})", w.name, tworld.name),
                    fact: slot_name(prog, tw, slot),
                    steps: steps.clone(),
                    rows,
                });
            }
        }
    }
    grids
}

fn slot_name(prog: &Program, wid: usize, s: usize) -> String {
    let sl = &prog.worlds[wid].slots[s];
    if sl.args.is_empty() {
        sl.fact.clone()
    } else {
        format!(
            "{}({})",
            sl.fact,
            sl.args
                .iter()
                .map(|a| prog.show(a))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub fn timeline_text(grids: &[Grid]) -> String {
    let mut out = String::new();
    for g in grids {
        if g.world == "main" {
            out.push_str(&format!("{}\n", g.fact));
        } else {
            out.push_str(&format!("{} — {}\n", g.world, g.fact));
        }
        let name_w = g
            .rows
            .iter()
            .map(|r| r.0.chars().count())
            .max()
            .unwrap_or(5)
            .max(5);
        let col_w: Vec<usize> = (0..g.steps.len())
            .map(|i| {
                g.rows
                    .iter()
                    .map(|r| r.1[i].text.chars().count() + 1)
                    .max()
                    .unwrap_or(1)
                    .max(g.steps[i].chars().count())
            })
            .collect();
        out.push_str(&format!("  {:<name_w$}", "", name_w = name_w));
        for (i, s) in g.steps.iter().enumerate() {
            out.push_str(&format!(" {:<w$}", s, w = col_w[i]));
        }
        out.push('\n');
        for (name, cells) in &g.rows {
            out.push_str(&format!("  {:<name_w$}", name, name_w = name_w));
            for (i, c) in cells.iter().enumerate() {
                let t = if c.kind == CellKind::Wrong {
                    format!("{}!", c.text)
                } else {
                    c.text.clone()
                };
                out.push_str(&format!(" {:<w$}", t, w = col_w[i]));
            }
            out.push('\n');
        }
        out.push('\n');
    }
    out.push_str("! = a false belief   ? = unsure   ⊥ = contradictory beliefs\n");
    out
}

fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

pub fn timeline_html(file: &str, grids: &[Grid]) -> String {
    let mut body = String::new();
    let mut last_world = String::new();
    for g in grids {
        if g.world != last_world {
            body.push_str(&format!("<h2>{}</h2>\n", esc(&g.world)));
            last_world = g.world.clone();
        }
        body.push_str(&format!(
            "<section><h3>{}</h3><div class=\"scroll\"><table><thead><tr><th></th>",
            esc(&g.fact)
        ));
        for s in &g.steps {
            body.push_str(&format!("<th>{}</th>", esc(s)));
        }
        body.push_str("</tr></thead><tbody>");
        for (name, cells) in &g.rows {
            body.push_str(&format!("<tr><th>{}</th>", esc(name)));
            for c in cells {
                let cls = match c.kind {
                    CellKind::Truth => "truth",
                    CellKind::Right => "right",
                    CellKind::Wrong => "wrong",
                    CellKind::Unsure => "unsure",
                    CellKind::Broken => "broken",
                };
                body.push_str(&format!("<td class=\"{}\">{}</td>", cls, esc(&c.text)));
            }
            body.push_str("</tr>");
        }
        body.push_str("</tbody></table></div></section>\n");
    }
    format!(
        r#"<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Who knows what</title>
<style>
:root {{ --bg:#fbfaf7; --fg:#1d1d1b; --muted:#6b6a65; --line:#e3e1da; --right:#dcefdc; --right-fg:#1f5a28; --wrong:#f6d6d2; --wrong-fg:#8a1f12; --unsure:#efeee9; --truth:#e7ecf5; }}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{ --bg:#161614; --fg:#ecebe6; --muted:#9a9890; --line:#2e2d29; --right:#1e3b22; --right-fg:#a8dcae; --wrong:#4a1f1a; --wrong-fg:#f3b3a9; --unsure:#262522; --truth:#1f2738; }} }}
:root[data-theme="dark"] {{ --bg:#161614; --fg:#ecebe6; --muted:#9a9890; --line:#2e2d29; --right:#1e3b22; --right-fg:#a8dcae; --wrong:#4a1f1a; --wrong-fg:#f3b3a9; --unsure:#262522; --truth:#1f2738; }}
body {{ background:var(--bg); color:var(--fg); font:15px/1.45 system-ui, sans-serif; margin:0; padding:24px 16px 48px; }}
main {{ max-width:1100px; margin:0 auto; }}
h1 {{ font-size:1.4rem; margin:0 0 4px; }} h2 {{ font-size:1.1rem; margin:32px 0 8px; }} h3 {{ font-size:.95rem; margin:18px 0 6px; font-family:ui-monospace, monospace; }}
p.sub {{ color:var(--muted); margin:0 0 16px; }}
.legend span {{ display:inline-block; padding:2px 8px; border-radius:4px; margin-right:6px; font-size:.85rem; }}
.scroll {{ overflow-x:auto; }}
table {{ border-collapse:collapse; font-family:ui-monospace, monospace; font-size:.85rem; }}
th, td {{ border:1px solid var(--line); padding:3px 8px; text-align:left; white-space:nowrap; }}
thead th {{ color:var(--muted); font-weight:500; }}
tbody th {{ font-weight:600; }}
td.truth {{ background:var(--truth); }} td.right {{ background:var(--right); color:var(--right-fg); }}
td.wrong {{ background:var(--wrong); color:var(--wrong-fg); font-weight:600; }} td.unsure {{ background:var(--unsure); color:var(--muted); }}
td.broken {{ background:var(--wrong); color:var(--wrong-fg); }}
</style></head><body><main>
<h1>Who knows what</h1>
<p class="sub">{}</p>
<p class="legend"><span class="right" style="background:var(--right);color:var(--right-fg)">true belief</span><span style="background:var(--wrong);color:var(--wrong-fg)">false belief</span><span style="background:var(--unsure);color:var(--muted)">? unsure</span><span style="background:var(--truth)">what is true</span></p>
{}
</main></body></html>
"#,
        esc(file),
        body
    )
}

pub fn parse_change(
    drop: Option<String>,
    mv: Option<String>,
    after: Option<String>,
) -> Result<Change, String> {
    match (drop, mv, after) {
        (Some(d), None, None) => Ok(Change::Drop(d)),
        (None, Some(m), Some(a)) => Ok(Change::Move(m, a)),
        _ => Err("use --drop EVENT, or --move EVENT --after EVENT".into()),
    }
}

pub fn timeline_json(grids: &[Grid]) -> crate::json::J {
    use crate::json::{obj, s, strs, J};
    J::Arr(
        grids
            .iter()
            .map(|g| {
                obj(vec![
                    ("world", s(g.world.clone())),
                    ("fact", s(g.fact.clone())),
                    ("steps", strs(g.steps.clone())),
                    (
                        "rows",
                        J::Arr(
                            g.rows
                                .iter()
                                .map(|(name, cells)| {
                                    obj(vec![
                                        ("who", s(name.clone())),
                                        (
                                            "cells",
                                            J::Arr(
                                                cells
                                                    .iter()
                                                    .map(|c| {
                                                        obj(vec![
                                                            ("value", s(c.text.clone())),
                                                            (
                                                                "kind",
                                                                s(match c.kind {
                                                                    CellKind::Truth => "truth",
                                                                    CellKind::Right => "right",
                                                                    CellKind::Wrong => "wrong",
                                                                    CellKind::Unsure => "unsure",
                                                                    CellKind::Broken => "contradictory",
                                                                }),
                                                            ),
                                                        ])
                                                    })
                                                    .collect(),
                                            ),
                                        ),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ])
            })
            .collect(),
    )
}
