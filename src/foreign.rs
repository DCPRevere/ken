//! A person's beliefs about another world: the reader about the tale.
//!
//! Beliefs come from the views the person was told (their effects and
//! preconditions), plus their own conclusions. Reasoning is three-valued:
//! anything not established is unknown.

use crate::ast::*;
use crate::state::ForeignStore;
use crate::value::*;
use crate::world::*;
use std::collections::HashMap;
use std::rc::Rc;

type Known = HashMap<usize, Value>;

/// Facts established by the views alone.
pub fn observed(prog: &Program, tw: usize, st: &ForeignStore) -> Known {
    let w = &prog.worlds[tw];
    let mut views: Vec<&(Vec<ActionInst>, usize)> = st.views.values().collect();
    views.sort_by_key(|v| v.1);
    let mut known = Known::new();
    for (acts, _) in views {
        for a in acts {
            let Some(info) = w.actions.get(&*a.name) else { continue };
            let env: Env = info.params.iter().zip(a.args.iter()).map(|((n, _), v)| (Rc::from(n.as_str()), v.clone())).collect();
            for n in &info.needs {
                learn_from_needs(prog, tw, &mut known, &env, n);
            }
            for eff in &info.effects {
                if let (Some(slot), Some(v)) = (slot_of(prog, tw, &known, &env, &eff.target), eval3(prog, tw, &known, &env, &eff.value)) {
                    known.insert(slot, v);
                }
            }
        }
    }
    known
}

fn learn_from_needs(prog: &Program, tw: usize, known: &mut Known, env: &Env, e: &E) {
    match &e.kind {
        ExprKind::Bin(BinOp::And, a, b) => {
            learn_from_needs(prog, tw, known, env, a);
            learn_from_needs(prog, tw, known, env, b);
        }
        ExprKind::Bin(BinOp::Eq, a, b) => {
            if let (Some(s), Some(v)) = (slot_of(prog, tw, known, env, a), eval3(prog, tw, known, env, b)) {
                known.insert(s, v);
            } else if let (Some(s), Some(v)) = (slot_of(prog, tw, known, env, b), eval3(prog, tw, known, env, a)) {
                known.insert(s, v);
            }
        }
        ExprKind::Not(a) => {
            if let Some(s) = slot_of(prog, tw, known, env, a) {
                known.insert(s, Value::Bool(false));
            }
        }
        ExprKind::Name(_) | ExprKind::Call(..) => {
            if let Some(s) = slot_of(prog, tw, known, env, e) {
                if prog.worlds[tw].slots[s].domain.first() == Some(&Value::Bool(false)) {
                    known.insert(s, Value::Bool(true));
                }
            }
        }
        _ => {}
    }
}

fn slot_of(prog: &Program, tw: usize, known: &Known, env: &Env, e: &E) -> Option<usize> {
    let w = &prog.worlds[tw];
    match &e.kind {
        ExprKind::Name(n) if env_get(env, n).is_none() && w.facts.contains_key(n) => w.slot_of.get(&(n.clone(), vec![])).copied(),
        ExprKind::Call(n, args) if w.facts.contains_key(n) => {
            let f = &w.facts[n];
            let mut vs = vec![];
            for (a, t) in args.iter().zip(f.params.iter()) {
                vs.push(crate::eval::coerce(w, t, eval3(prog, tw, known, env, a)?));
            }
            w.slot_of.get(&(n.clone(), vs)).copied()
        }
        _ => None,
    }
}

/// Literal facts a conclusion asserts.
fn literals(prog: &Program, tw: usize, env: &Env, e: &E, out: &mut Known) {
    let empty = Known::new();
    match &e.kind {
        ExprKind::Bin(BinOp::And, a, b) => {
            literals(prog, tw, env, a, out);
            literals(prog, tw, env, b, out);
        }
        ExprKind::Not(a) => {
            if let Some(s) = slot_of(prog, tw, &empty, env, a) {
                out.insert(s, Value::Bool(false));
            }
        }
        ExprKind::Bin(BinOp::Eq, a, b) => {
            if let (Some(s), Some(v)) = (slot_of(prog, tw, &empty, env, a), eval3(prog, tw, &empty, env, b)) {
                out.insert(s, v);
            }
        }
        ExprKind::Name(_) | ExprKind::Call(..) => {
            if let Some(s) = slot_of(prog, tw, &empty, env, e) {
                out.insert(s, Value::Bool(true));
            }
        }
        _ => {}
    }
}

fn with_conclusions(prog: &Program, tw: usize, st: &ForeignStore) -> Known {
    let mut k = observed(prog, tw, st);
    for c in &st.active {
        if let Value::Formula(f) = &c.formula {
            literals(prog, tw, &f.env, &f.expr, &mut k);
        }
    }
    k
}

pub fn believes(prog: &Program, tw: usize, st: &ForeignStore, env: &Env, e: &E) -> bool {
    let text = prog.text(e.span);
    if st.active.iter().any(|c| matches!(&c.formula, Value::Formula(f) if prog.text(f.expr.span) == text)) {
        return true;
    }
    let k = with_conclusions(prog, tw, st);
    eval3(prog, tw, &k, env, e) == Some(Value::Bool(true))
}

pub fn believes_not(prog: &Program, tw: usize, st: &ForeignStore, env: &Env, e: &E) -> bool {
    let k = with_conclusions(prog, tw, st);
    eval3(prog, tw, &k, env, e) == Some(Value::Bool(false))
}

/// Evaluate using observations only (for `deducible by` and `possible for`).
pub fn eval_obs(prog: &Program, tw: usize, st: &ForeignStore, env: &Env, e: &E) -> Option<bool> {
    let k = observed(prog, tw, st);
    eval3(prog, tw, &k, env, e).and_then(|v| v.as_bool())
}

/// Three-valued evaluation: None means unknown.
pub fn eval3(prog: &Program, tw: usize, known: &Known, env: &Env, e: &E) -> Option<Value> {
    let w = &prog.worlds[tw];
    match &e.kind {
        ExprKind::Int(n) => Some(Value::Int(*n)),
        ExprKind::Bool(b) => Some(Value::Bool(*b)),
        ExprKind::Name(n) => {
            if let Some(v) = env_get(env, n) {
                return Some(v.clone());
            }
            if let Some(v) = prog.params.get(n) {
                return Some(Value::Int(*v));
            }
            if w.facts.contains_key(n) {
                return known.get(w.slot_of.get(&(n.clone(), vec![]))?).cloned();
            }
            if let Some(a) = w.agent_names.get(n) {
                return Some(Value::Agent(tw as u16, *a));
            }
            if w.consts.contains_key(n) {
                return Some(Value::Sym(Rc::from(n.as_str())));
            }
            None
        }
        ExprKind::Call(..) => known.get(&slot_of(prog, tw, known, env, e)?).cloned(),
        ExprKind::Index(g, i) => {
            let k = eval3(prog, tw, known, env, i)?.as_int()?;
            w.agent_names.get(&format!("{}[{}]", g, k)).map(|a| Value::Agent(tw as u16, *a))
        }
        ExprKind::Tuple(xs) => {
            let mut vs = vec![];
            for x in xs {
                vs.push(eval3(prog, tw, known, env, x)?);
            }
            Some(Value::Tuple(vs.into()))
        }
        ExprKind::Not(a) => Some(Value::Bool(!eval3(prog, tw, known, env, a)?.as_bool()?)),
        ExprKind::Bin(op, a, b) => {
            let x = eval3(prog, tw, known, env, a);
            let y = eval3(prog, tw, known, env, b);
            let xb = x.as_ref().and_then(|v| v.as_bool());
            let yb = y.as_ref().and_then(|v| v.as_bool());
            match op {
                BinOp::And => match (xb, yb) {
                    (Some(false), _) | (_, Some(false)) => Some(Value::Bool(false)),
                    (Some(true), Some(true)) => Some(Value::Bool(true)),
                    _ => None,
                },
                BinOp::Or => match (xb, yb) {
                    (Some(true), _) | (_, Some(true)) => Some(Value::Bool(true)),
                    (Some(false), Some(false)) => Some(Value::Bool(false)),
                    _ => None,
                },
                BinOp::Implies => match (xb, yb) {
                    (Some(false), _) | (_, Some(true)) => Some(Value::Bool(true)),
                    (Some(true), Some(false)) => Some(Value::Bool(false)),
                    _ => None,
                },
                BinOp::Iff => Some(Value::Bool(xb? == yb?)),
                BinOp::Eq => Some(Value::Bool(x? == y?)),
                BinOp::Ne => Some(Value::Bool(x? != y?)),
                _ => {
                    let (x, y) = (x?.as_int()?, y?.as_int()?);
                    Some(match op {
                        BinOp::Lt => Value::Bool(x < y),
                        BinOp::Le => Value::Bool(x <= y),
                        BinOp::Gt => Value::Bool(x > y),
                        BinOp::Ge => Value::Bool(x >= y),
                        BinOp::Add => Value::Int(x + y),
                        BinOp::Sub => Value::Int(x - y),
                        _ => Value::Int(x * y),
                    })
                }
            }
        }
        ExprKind::Quant { all, var, ty, body } => {
            let t = resolve_ty(w, ty, &prog.params, 0).ok()?;
            let dom = domain_of(w, &t)?;
            let mut unknown = false;
            for v in dom {
                match eval3(prog, tw, known, &env_with(env, var, v), body).and_then(|x| x.as_bool()) {
                    Some(b) if b != *all => return Some(Value::Bool(!*all)),
                    Some(_) => {}
                    None => unknown = true,
                }
            }
            if unknown { None } else { Some(Value::Bool(*all)) }
        }
        _ => None,
    }
}
