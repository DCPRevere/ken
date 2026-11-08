//! Possible-worlds (Kripke) models, product update and contraction.

use crate::value::Value;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Model {
    pub vals: Vec<Rc<[Value]>>,
    /// rel[agent][world] = sorted successor worlds
    pub rel: Vec<Vec<Vec<u32>>>,
    pub actual: u32,
}

impl Model {
    pub fn n(&self) -> usize {
        self.vals.len()
    }
    pub fn succ(&self, a: u32, w: u32) -> &[u32] {
        &self.rel[a as usize][w as usize]
    }
    pub fn n_agents(&self) -> usize {
        self.rel.len()
    }
}

/// Supplies the event side of a product update.
pub trait Scenarios {
    type S: Clone + Eq + Hash;
    fn perceive(&mut self, m: &Model, agent: u32, s: &Self::S, w: u32) -> Result<Vec<Self::S>, String>;
    fn pre(&mut self, m: &Model, s: &Self::S, w: u32) -> Result<bool, String>;
    fn post(&mut self, m: &Model, s: &Self::S, w: u32) -> Result<Rc<[Value]>, String>;
}

/// Product update from the actual world paired with the real scenario.
/// Only nodes reachable from the actual node are built.
pub fn product<X: Scenarios>(m: &Model, real: X::S, sc: &mut X) -> Result<(Model, Vec<(u32, X::S)>), String> {
    let na = m.n_agents();
    let mut ids: HashMap<(u32, X::S), u32> = HashMap::new();
    let mut nodes: Vec<(u32, X::S)> = Vec::new();
    let mut pre_cache: HashMap<(u32, X::S), bool> = HashMap::new();
    let mut succs: Vec<Vec<Vec<u32>>> = Vec::new();
    ids.insert((m.actual, real.clone()), 0);
    nodes.push((m.actual, real));
    let mut i = 0;
    while i < nodes.len() {
        let (w, s) = nodes[i].clone();
        let mut per_agent = Vec::with_capacity(na);
        for a in 0..na as u32 {
            let ps = sc.perceive(m, a, &s, w)?;
            let mut out = Vec::new();
            for &w2 in m.succ(a, w) {
                for s2 in &ps {
                    let key = (w2, s2.clone());
                    if let Some(&id) = ids.get(&key) {
                        out.push(id);
                        continue;
                    }
                    let ok = match pre_cache.get(&key) {
                        Some(b) => *b,
                        None => {
                            let b = sc.pre(m, s2, w2)?;
                            pre_cache.insert(key.clone(), b);
                            b
                        }
                    };
                    if ok {
                        let id = nodes.len() as u32;
                        ids.insert(key.clone(), id);
                        nodes.push(key);
                        out.push(id);
                    }
                }
            }
            out.sort_unstable();
            out.dedup();
            per_agent.push(out);
        }
        succs.push(per_agent);
        i += 1;
        if nodes.len() > 2_000_000 {
            return Err("the model grew past 2,000,000 possible worlds; simplify the story or reduce parameters".into());
        }
    }
    let mut vals = Vec::with_capacity(nodes.len());
    for (w, s) in &nodes {
        vals.push(sc.post(m, s, *w)?);
    }
    let mut rel = vec![vec![Vec::new(); nodes.len()]; na];
    for (n, per) in succs.into_iter().enumerate() {
        for (a, out) in per.into_iter().enumerate() {
            rel[a][n] = out;
        }
    }
    Ok((Model { vals, rel, actual: 0 }, nodes))
}

/// Keep only worlds reachable from the actual one, then merge bisimilar worlds.
pub fn contract(m: &Model) -> Model {
    let na = m.n_agents();
    // reachability
    let mut keep = vec![false; m.n()];
    let mut stack = vec![m.actual];
    keep[m.actual as usize] = true;
    while let Some(w) = stack.pop() {
        for a in 0..na {
            for &v in &m.rel[a][w as usize] {
                if !keep[v as usize] {
                    keep[v as usize] = true;
                    stack.push(v);
                }
            }
        }
    }
    // partition refinement
    let mut block: Vec<u32> = vec![u32::MAX; m.n()];
    {
        let mut by_val: HashMap<&[Value], u32> = HashMap::new();
        for w in 0..m.n() {
            if !keep[w] {
                continue;
            }
            let n = by_val.len() as u32;
            block[w] = *by_val.entry(&m.vals[w][..]).or_insert(n);
        }
    }
    let mut count = block.iter().filter(|b| **b != u32::MAX).collect::<std::collections::HashSet<_>>().len();
    loop {
        let mut sigs: HashMap<(u32, Vec<Vec<u32>>), u32> = HashMap::new();
        let mut nb = vec![u32::MAX; m.n()];
        for w in 0..m.n() {
            if !keep[w] {
                continue;
            }
            let mut sig = Vec::with_capacity(na);
            for a in 0..na {
                let mut bs: Vec<u32> = m.rel[a][w].iter().map(|v| block[*v as usize]).collect();
                bs.sort_unstable();
                bs.dedup();
                sig.push(bs);
            }
            let n = sigs.len() as u32;
            nb[w] = *sigs.entry((block[w], sig)).or_insert(n);
        }
        let nc = sigs.len();
        block = nb;
        if nc == count {
            break;
        }
        count = nc;
    }
    let mut rep: Vec<Option<usize>> = vec![None; count];
    for w in 0..m.n() {
        if keep[w] && rep[block[w] as usize].is_none() {
            rep[block[w] as usize] = Some(w);
        }
    }
    let vals: Vec<Rc<[Value]>> = rep.iter().map(|r| m.vals[r.unwrap()].clone()).collect();
    let mut rel = vec![vec![Vec::new(); count]; na];
    for (b, r) in rep.iter().enumerate() {
        let w = r.unwrap();
        for a in 0..na {
            let mut bs: Vec<u32> = m.rel[a][w].iter().map(|v| block[*v as usize]).collect();
            bs.sort_unstable();
            bs.dedup();
            rel[a][b] = bs;
        }
    }
    Model { vals, rel, actual: block[m.actual as usize] }
}
