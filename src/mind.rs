//! `ken mind`: what one character knows, believes, suspects and wants at each step.
//! Written for whoever is writing the scene: before writing from Aubrey's point of
//! view at r1, ask what Aubrey has in his head at r1.

use crate::check::{Checker, Engine};
use crate::json::{obj, s, strs, J};
use crate::kripke::Model;
use crate::state::{Level, Snap};
use crate::value::Value;
use crate::ast::Mode;
use crate::world::Program;

/// One agent's state about one fact.
#[derive(Clone, PartialEq)]
enum Held {
    /// believes this value (right or wrong is decided against the truth)
    Is(Value),
    /// several values are possible
    Unsure(Vec<Value>),
    /// no possible world left: contradictory beliefs
    Broken,
}

fn held(m: &Model, a: u32, w: u32, slot: usize) -> Held {
    let succ = m.succ(a, w);
    if succ.is_empty() {
        return Held::Broken;
    }
    let mut vs: Vec<Value> = vec![];
    for v in succ {
        let x = &m.vals[*v as usize][slot];
        if !vs.contains(x) {
            vs.push(x.clone());
        }
    }
    if vs.len() == 1 {
        Held::Is(vs.pop().unwrap())
    } else {
        Held::Unsure(vs)
    }
}

pub struct Fact {
    pub fact: String,
    pub held: String,
    pub truth: String,
    /// "knows", "wrong", "unsure" or "contradictory"
    pub status: &'static str,
    pub possible: Vec<String>,
}

pub struct Other {
    pub agent: String,
    pub fact: String,
    pub thinks: String,
    pub actually: String,
}

pub struct About {
    pub world: String,
    pub fact: String,
    pub believes: String,
    pub truth: String,
}

pub struct StepMind {
    pub label: String,
    pub happened: String,
    pub saw: Option<String>,
    pub facts: Vec<Fact>,
    pub suspects: Vec<String>,
    pub wants: Vec<String>,
    pub concludes: Vec<String>,
    pub others: Vec<Other>,
    pub about: Vec<About>,
    pub changes: Vec<String>,
}

pub struct Mind {
    pub file: String,
    pub world: String,
    pub agent: String,
    pub errors: usize,
    pub steps: Vec<StepMind>,
}

fn show_held(prog: &Program, h: &Held) -> String {
    match h {
        Held::Is(v) => prog.show(v),
        Held::Unsure(vs) => vs.iter().map(|v| prog.show(v)).collect::<Vec<_>>().join(" or "),
        Held::Broken => "⊥".into(),
    }
}

/// How one agent stands on a fact, said from the outside: "believes x = v" or "is unsure of x".
fn stance(prog: &Program, fact: &str, h: &Held) -> String {
    match h {
        Held::Is(v) => format!("believes {} = {}", fact, prog.show(v)),
        Held::Unsure(_) => format!("is unsure of {}", fact),
        Held::Broken => format!("has contradictory beliefs about {}", fact),
    }
}

pub fn find_agent(prog: &Program, name: &str, world: Option<&str>) -> Result<(usize, u32), String> {
    for (wid, w) in prog.worlds.iter().enumerate() {
        if let Some(wn) = world {
            if w.name != wn {
                continue;
            }
        }
        if let Some(&a) = w.agent_names.get(name) {
            return Ok((wid, a));
        }
    }
    Err(match world {
        Some(wn) => format!("no agent '{}' in world '{}'", name, wn),
        None => format!("no agent '{}'", name),
    })
}

pub fn mind(prog: &Program, file: &str, agent: &str, world: Option<&str>) -> Result<Mind, String> {
    let (wid, a) = find_agent(prog, agent, world)?;
    let checker = Checker::new(prog, Engine::Explicit);
    let report = checker.check();
    let w = &prog.worlds[wid];
    let run = checker
        .run_of(wid)
        .ok_or(format!("world '{}' could not be run", w.name))?;
    let mut slots: Vec<usize> = w.relevant.iter().copied().collect();
    slots.sort_by_key(|s| slot_name(prog, wid, *s));
    // `honest` only matters where somebody isn't
    slots.retain(|&slot| {
        w.slots[slot].fact != "honest"
            || run
                .snaps
                .iter()
                .any(|sn| sn.model.vals[sn.model.actual as usize][slot] != Value::Bool(true))
    });
    let names: Vec<String> = slots.iter().map(|s| slot_name(prog, wid, *s)).collect();
    let mut steps: Vec<StepMind> = vec![];
    for (t, sn) in run.snaps.iter().enumerate() {
        let label = w.steps[t].label.clone();
        let m = &sn.model;
        let truth = &m.vals[m.actual as usize];
        // what happened, and what this agent took it to be
        let happened = prog.show_actions(&sn.actual);
        let saw = sn.registry.views[a as usize]
            .get(&label)
            .filter(|v| v.step == t)
            .map(|v| prog.show_actions(&v.actions));
        // facts
        let mut facts = vec![];
        let mut helds = vec![];
        for (i, &slot) in slots.iter().enumerate() {
            let h = held(m, a, m.actual, slot);
            let tv = prog.show(&truth[slot]);
            let (status, possible) = match &h {
                Held::Is(v) if *v == truth[slot] => ("knows", vec![]),
                Held::Is(_) => ("wrong", vec![]),
                Held::Unsure(vs) => ("unsure", vs.iter().map(|v| prog.show(v)).collect()),
                Held::Broken => ("contradictory", vec![]),
            };
            facts.push(Fact {
                fact: names[i].clone(),
                held: show_held(prog, &h),
                truth: tv,
                status,
                possible,
            });
            helds.push(h);
        }
        // what they think the others believe, where it differs from their own view
        // or from what the other really believes
        let mut others = vec![];
        let mine = m.succ(a, m.actual);
        if !mine.is_empty() {
            for (b, bi) in w.agents.iter().enumerate() {
                let b = b as u32;
                if b == a || bi.sees_all_of.is_some() {
                    continue;
                }
                for (i, &slot) in slots.iter().enumerate() {
                    let first = held(m, b, mine[0], slot);
                    if mine[1..].iter().any(|&x| held(m, b, x, slot) != first) {
                        continue; // they don't know what b thinks
                    }
                    let actual = held(m, b, m.actual, slot);
                    let right = matches!(&helds[i], Held::Is(v) if *v == truth[slot]);
                    let show = if first == helds[i] {
                        // they think b agrees with them: only news if they are right and b isn't
                        right && actual != first
                    } else {
                        // they think b differs: news unless they rightly think b is unsure
                        !(matches!(first, Held::Unsure(_)) && first == actual)
                    };
                    if !show {
                        continue;
                    }
                    others.push(Other {
                        agent: bi.name.clone(),
                        fact: names[i].clone(),
                        thinks: stance(prog, &names[i], &first),
                        actually: stance(prog, &names[i], &actual),
                    });
                }
            }
        }
        let reg = &sn.registry;
        let suspects: Vec<String> = reg.suspicions[a as usize]
            .iter()
            .map(|r| prog.show(&r.formula))
            .collect();
        let wants: Vec<String> = reg.wants[a as usize]
            .iter()
            .map(|r| prog.show(&r.formula))
            .collect();
        let concludes: Vec<String> = run
            .conclusions
            .iter()
            .filter(|c| c.agent == a && c.step == t && !sn.disabled.contains(&c.key))
            .map(|c| prog.show(&c.formula))
            .collect();
        let about = foreign(prog, &checker, wid, a, sn);
        steps.push(StepMind {
            label,
            happened,
            saw,
            facts,
            suspects,
            wants,
            concludes,
            others,
            about,
            changes: vec![],
        });
    }
    for t in 0..steps.len() {
        let ch = if t == 0 {
            vec![]
        } else {
            changes(&steps[t - 1], &steps[t])
        };
        steps[t].changes = ch;
    }
    let errors = report
        .diags
        .iter()
        .filter(|d| d.level == Level::Error)
        .count();
    Ok(Mind {
        file: file.to_string(),
        world: w.name.clone(),
        agent: agent.to_string(),
        errors,
        steps,
    })
}

/// A reader's beliefs about the tale they are being told.
fn foreign(prog: &Program, checker: &Checker, wid: usize, a: u32, sn: &Snap) -> Vec<About> {
    let w = &prog.worlds[wid];
    let mut out = vec![];
    if w.agents[a as usize].mode != Mode::Person {
        return out;
    }
    for &tw in &w.about {
        if w.agents[a as usize].sees_all_of == Some(tw) {
            continue;
        }
        let Some(trun) = checker.run_of(tw) else { continue };
        let tlast = trun
            .snaps
            .last()
            .map(|s| s.model.vals[s.model.actual as usize].to_vec())
            .unwrap_or_default();
        let st = sn.foreign.get(&(a, tw)).cloned().unwrap_or_default();
        let k = crate::foreign::with_conclusions(prog, tw, &st);
        let mut ks: Vec<(&usize, &Value)> = k.iter().collect();
        ks.sort_by_key(|(s, _)| slot_name(prog, tw, **s));
        for (slot, v) in ks {
            out.push(About {
                world: prog.worlds[tw].name.clone(),
                fact: slot_name(prog, tw, *slot),
                believes: prog.show(v),
                truth: tlast.get(*slot).map(|x| prog.show(x)).unwrap_or("?".into()),
            });
        }
    }
    out
}

fn changes(prev: &StepMind, now: &StepMind) -> Vec<String> {
    let mut out = vec![];
    for (p, n) in prev.facts.iter().zip(&now.facts) {
        if p.held == n.held && p.status == n.status {
            continue;
        }
        let line = match n.status {
            "knows" if p.held == n.held => format!("is right again: {} = {}", n.fact, n.held),
            "knows" => format!("learns {} = {}", n.fact, n.held),
            "wrong" if p.held == n.held => format!(
                "still thinks {} = {}, but it is now {}",
                n.fact, n.held, n.truth
            ),
            "wrong" => format!(
                "comes to believe {} = {} (wrongly: it is {})",
                n.fact, n.held, n.truth
            ),
            "unsure" if p.status == "unsure" => continue,
            "unsure" => format!("is no longer sure of {} ({})", n.fact, n.held),
            _ => format!("now has contradictory beliefs about {}", n.fact),
        };
        out.push(line);
    }
    for x in &now.suspects {
        if !prev.suspects.contains(x) {
            out.push(format!("starts to suspect {}", x));
        }
    }
    for x in &prev.suspects {
        if !now.suspects.contains(x) {
            out.push(format!("no longer suspects {}", x));
        }
    }
    for x in &now.wants {
        if !prev.wants.contains(x) {
            out.push(format!("starts to want {}", x));
        }
    }
    for x in &prev.wants {
        if !now.wants.contains(x) {
            out.push(format!("no longer wants {}", x));
        }
    }
    for c in &now.concludes {
        out.push(format!("concludes {}", c));
    }
    for o in &now.others {
        let before = prev
            .others
            .iter()
            .find(|q| q.agent == o.agent && q.fact == o.fact);
        if before.map(|q| &q.thinks) != Some(&o.thinks) {
            out.push(format!("now thinks {} {}{}", o.agent, o.thinks, mistaken(o)));
        }
    }
    for x in &now.about {
        let before = prev
            .about
            .iter()
            .find(|q| q.world == x.world && q.fact == x.fact);
        if before.map(|q| &q.believes) != Some(&x.believes) {
            out.push(format!(
                "now believes {}: {} = {}{}",
                x.world,
                x.fact,
                x.believes,
                if x.believes == x.truth { "" } else { " (wrongly)" }
            ));
        }
    }
    out
}

fn mistaken(o: &Other) -> String {
    if o.thinks == o.actually {
        String::new()
    } else {
        format!(" (wrongly: {} {})", o.agent, o.actually)
    }
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

// ------------------------------------------------------------------ output

fn event_line(m: &Mind, st: &StepMind) -> String {
    if st.label == "start" {
        return "start".into();
    }
    let seen = match &st.saw {
        None => format!("{} didn't see it", m.agent),
        Some(v) if *v == st.happened => format!("{} saw it", m.agent),
        Some(v) => format!("{} took it for {}", m.agent, v),
    };
    format!("{}: {} ({})", st.label, st.happened, seen)
}

fn full(m: &Mind, st: &StepMind, out: &mut String) {
    let pick = |status: &'static str| st.facts.iter().filter(move |f| f.status == status);
    let knows: Vec<String> = pick("knows").map(|f| format!("{} = {}", f.fact, f.held)).collect();
    let wrong: Vec<String> = pick("wrong")
        .map(|f| format!("{} = {} (really {})", f.fact, f.held, f.truth))
        .collect();
    let unsure: Vec<String> = pick("unsure")
        .map(|f| format!("{} ({}; really {})", f.fact, f.held, f.truth))
        .collect();
    let broken: Vec<String> = pick("contradictory").map(|f| f.fact.clone()).collect();
    let others: Vec<String> = st
        .others
        .iter()
        .map(|o| format!("{} {}{}", o.agent, o.thinks, mistaken(o)))
        .collect();
    let about: Vec<String> = st
        .about
        .iter()
        .map(|x| {
            format!(
                "{}: {} = {}{}",
                x.world,
                x.fact,
                x.believes,
                if x.believes == x.truth { "" } else { " (wrongly)" }
            )
        })
        .collect();
    let rows: [(&str, &Vec<String>); 9] = [
        ("knows", &knows),
        ("wrongly believes", &wrong),
        ("unsure of", &unsure),
        ("contradictory about", &broken),
        ("suspects", &st.suspects),
        ("wants", &st.wants),
        ("concludes", &st.concludes),
        ("thinks", &others),
        ("about the tale", &about),
    ];
    let _ = m;
    for (head, xs) in rows {
        if xs.is_empty() {
            continue;
        }
        out.push_str(&format!("  {}:\n", head));
        for x in xs {
            out.push_str(&format!("    {}\n", x));
        }
    }
}

/// Text: the full picture at the start (or at one step), then only what changes.
pub fn text(m: &Mind, at: Option<usize>) -> String {
    let mut out = format!("{} ({}, world {})\n", m.agent, m.file, m.world);
    if m.errors > 0 {
        out.push_str(&format!(
            "warning: the story has {} error(s); run `ken check` first, as this may be wrong\n",
            m.errors
        ));
    }
    out.push('\n');
    match at {
        Some(t) => {
            let st = &m.steps[t];
            out.push_str(&format!("{}\n", event_line(m, st)));
            full(m, st, &mut out);
        }
        None => {
            for (t, st) in m.steps.iter().enumerate() {
                out.push_str(&format!("{}\n", event_line(m, st)));
                if t == 0 {
                    full(m, st, &mut out);
                } else if st.changes.is_empty() {
                    out.push_str("  (nothing changes)\n");
                } else {
                    for c in &st.changes {
                        out.push_str(&format!("  {}\n", c));
                    }
                }
            }
            out.push_str("\nUse --at EVENT for the full picture at one point.\n");
        }
    }
    out
}

pub fn json(m: &Mind, at: Option<usize>) -> J {
    let steps: Vec<&StepMind> = match at {
        Some(t) => vec![&m.steps[t]],
        None => m.steps.iter().collect(),
    };
    let steps = steps
        .into_iter()
        .map(|st| {
            let by = |status: &str| -> Vec<&Fact> {
                st.facts.iter().filter(|f| f.status == status).collect()
            };
            obj(vec![
                ("label", s(st.label.clone())),
                ("happened", s(st.happened.clone())),
                ("saw", st.saw.clone().map(J::Str).unwrap_or(J::Null)),
                (
                    "knows",
                    J::Arr(
                        by("knows")
                            .iter()
                            .map(|f| obj(vec![("fact", s(f.fact.clone())), ("value", s(f.held.clone()))]))
                            .collect(),
                    ),
                ),
                (
                    "wrong",
                    J::Arr(
                        by("wrong")
                            .iter()
                            .map(|f| {
                                obj(vec![
                                    ("fact", s(f.fact.clone())),
                                    ("believes", s(f.held.clone())),
                                    ("truth", s(f.truth.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "unsure",
                    J::Arr(
                        by("unsure")
                            .iter()
                            .map(|f| {
                                obj(vec![
                                    ("fact", s(f.fact.clone())),
                                    ("possible", strs(f.possible.clone())),
                                    ("truth", s(f.truth.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "contradictory",
                    strs(by("contradictory").iter().map(|f| f.fact.clone())),
                ),
                ("suspects", strs(st.suspects.clone())),
                ("wants", strs(st.wants.clone())),
                ("concludes", strs(st.concludes.clone())),
                (
                    "thinks_others",
                    J::Arr(
                        st.others
                            .iter()
                            .map(|o| {
                                obj(vec![
                                    ("agent", s(o.agent.clone())),
                                    ("fact", s(o.fact.clone())),
                                    ("thinks", s(o.thinks.clone())),
                                    ("actually", s(o.actually.clone())),
                                    ("right", J::Bool(o.thinks == o.actually)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "about",
                    J::Arr(
                        st.about
                            .iter()
                            .map(|x| {
                                obj(vec![
                                    ("world", s(x.world.clone())),
                                    ("fact", s(x.fact.clone())),
                                    ("believes", s(x.believes.clone())),
                                    ("truth", s(x.truth.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
                ("changes", strs(st.changes.clone())),
            ])
        })
        .collect();
    obj(vec![
        ("file", s(m.file.clone())),
        ("world", s(m.world.clone())),
        ("agent", s(m.agent.clone())),
        ("errors", J::Num(m.errors as i64)),
        ("steps", J::Arr(steps)),
    ])
}
