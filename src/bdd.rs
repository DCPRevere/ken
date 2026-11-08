//! Reduced ordered binary decision diagrams with complement edges.
//!
//! A reference `B` is a node index shifted left by one, with the low bit
//! meaning "negated". Negation is therefore free. Node 0 is the terminal
//! TRUE; FALSE is its negation. Stored nodes keep their `hi` edge regular,
//! which makes the representation canonical.
//!
//! Node indices are topologically ordered (children first), so garbage
//! collection compacts the table in one pass. Operation caches are lossy,
//! direct-mapped, and grow with the node table.

pub type B = u32;
pub const TRUE: B = 0;
pub const FALSE: B = 1;
const TERM: u32 = u32::MAX;

#[inline]
fn mix(a: u32, b: u32, c: u32) -> u64 {
    let mut h = (a as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    h ^= (b as u64).wrapping_mul(0xC2B2_AE3D_27D4_EB4F).rotate_left(21);
    h ^= (c as u64).wrapping_mul(0x1656_67B1_9E37_79F9).rotate_left(42);
    h ^ (h >> 29)
}

#[inline]
fn idx(f: B) -> usize {
    (f >> 1) as usize
}
#[inline]
fn neg(f: B) -> u32 {
    f & 1
}
#[inline]
fn is_const(f: B) -> bool {
    f <= FALSE
}

#[derive(Clone, Copy)]
struct Node {
    var: u32,
    lo: B,
    hi: B, // always regular
}

/// Open-addressing table; each slot holds its key inline (one cache line per probe).
struct Unique {
    slots: Vec<[u32; 4]>, // var, lo, hi, id   (id == u32::MAX: empty)
    len: usize,
}

impl Unique {
    fn with_capacity(n: usize) -> Self {
        let cap = (n * 2).next_power_of_two().max(1 << 16);
        Unique { slots: vec![[0, 0, 0, u32::MAX]; cap], len: 0 }
    }
    #[inline]
    fn find(&self, _nodes: &[Node], var: u32, lo: B, hi: B) -> Result<u32, usize> {
        let mask = self.slots.len() - 1;
        let mut i = (mix(var, lo, hi) as usize) & mask;
        loop {
            let s = self.slots[i];
            if s[3] == u32::MAX {
                return Err(i);
            }
            if s[0] == var && s[1] == lo && s[2] == hi {
                return Ok(s[3]);
            }
            i = (i + 1) & mask;
        }
    }
    fn insert_at(&mut self, i: usize, id: u32, nodes: &[Node]) {
        let n = nodes[id as usize];
        self.slots[i] = [n.var, n.lo, n.hi, id];
        self.len += 1;
        if self.len * 10 > self.slots.len() * 7 {
            let cap = self.slots.len() * 2;
            let old = std::mem::replace(&mut self.slots, vec![[0, 0, 0, u32::MAX]; cap]);
            let mask = cap - 1;
            for s in old.into_iter().filter(|x| x[3] != u32::MAX) {
                let mut j = (mix(s[0], s[1], s[2]) as usize) & mask;
                while self.slots[j][3] != u32::MAX {
                    j = (j + 1) & mask;
                }
                self.slots[j] = s;
            }
        }
    }
}

/// A lossy direct-mapped cache of (a, b, c) -> r.
struct Cache {
    e: Vec<[u32; 4]>,
}
impl Cache {
    fn new(bits: u32) -> Self {
        Cache { e: vec![[u32::MAX; 4]; 1 << bits] }
    }
    #[inline]
    fn get(&self, a: u32, b: u32, c: u32) -> Option<u32> {
        let x = self.e[(mix(a, b, c) as usize) & (self.e.len() - 1)];
        if x[0] == a && x[1] == b && x[2] == c { Some(x[3]) } else { None }
    }
    #[inline]
    fn put(&mut self, a: u32, b: u32, c: u32, r: u32) {
        let n = self.e.len();
        self.e[(mix(a, b, c) as usize) & (n - 1)] = [a, b, c, r];
    }
    fn clear_resize(&mut self, bits: u32) {
        if self.e.len() != 1 << bits {
            self.e = vec![[u32::MAX; 4]; 1 << bits];
        } else {
            self.e.fill([u32::MAX; 4]);
        }
    }
    fn bits(&self) -> u32 {
        self.e.len().trailing_zeros()
    }
}

const MIN_BITS: u32 = 18;
const MAX_BITS: u32 = 24;

pub struct Bdd {
    nodes: Vec<Node>,
    unique: Unique,
    ite_c: Cache,
    quant_c: Cache,
    restrict_c: Cache,
    var_sets: Vec<Vec<bool>>,
    set_ids: std::collections::HashMap<Vec<u32>, u32>,
}

impl Default for Bdd {
    fn default() -> Self {
        Self::new()
    }
}

impl Bdd {
    pub fn new() -> Self {
        Bdd {
            nodes: vec![Node { var: TERM, lo: TRUE, hi: TRUE }],
            unique: Unique::with_capacity(1 << 16),
            ite_c: Cache::new(MIN_BITS),
            quant_c: Cache::new(MIN_BITS),
            restrict_c: Cache::new(MIN_BITS),
            var_sets: vec![],
            set_ids: Default::default(),
        }
    }

    /// Grow the caches as the table grows, so they keep their hit rate.
    fn maybe_grow_caches(&mut self) {
        let want = ((self.nodes.len() as u64).next_power_of_two().trailing_zeros()).clamp(MIN_BITS, MAX_BITS);
        if want > self.ite_c.bits() {
            self.ite_c.clear_resize(want);
            self.quant_c.clear_resize(want - 1);
            self.restrict_c.clear_resize(want - 1);
        }
    }

    fn mk(&mut self, var: u32, lo: B, hi: B) -> B {
        if lo == hi {
            return lo;
        }
        // canonical form: hi edge regular
        let (lo, hi, out) = if neg(hi) == 1 { (lo ^ 1, hi ^ 1, 1) } else { (lo, hi, 0) };
        let id = match self.unique.find(&self.nodes, var, lo, hi) {
            Ok(id) => id,
            Err(slot) => {
                let id = self.nodes.len() as u32;
                self.nodes.push(Node { var, lo, hi });
                self.unique.insert_at(slot, id, &self.nodes);
                if self.nodes.len().is_power_of_two() {
                    self.maybe_grow_caches();
                }
                id
            }
        };
        (id << 1) | out
    }

    pub fn var(&mut self, v: u32) -> B {
        self.mk(v, FALSE, TRUE)
    }

    #[inline]
    fn top(&self, f: B) -> u32 {
        self.nodes[idx(f)].var
    }

    #[inline]
    fn cof(&self, f: B, v: u32) -> (B, B) {
        let n = self.nodes[idx(f)];
        if n.var == v {
            let c = neg(f);
            (n.lo ^ c, n.hi ^ c)
        } else {
            (f, f)
        }
    }

    #[inline]
    pub fn not(&mut self, f: B) -> B {
        f ^ 1
    }

    pub fn ite(&mut self, f: B, g: B, h: B) -> B {
        // terminal cases
        if f == TRUE {
            return g;
        }
        if f == FALSE {
            return h;
        }
        let (mut g, mut h) = (g, h);
        if g == f {
            g = TRUE;
        } else if g == f ^ 1 {
            g = FALSE;
        }
        if h == f {
            h = FALSE;
        } else if h == f ^ 1 {
            h = TRUE;
        }
        if g == h {
            return g;
        }
        if g == TRUE && h == FALSE {
            return f;
        }
        if g == FALSE && h == TRUE {
            return f ^ 1;
        }
        // normalise: f regular; then g regular (negating the result)
        let (f, g, h) = if neg(f) == 1 { (f ^ 1, h, g) } else { (f, g, h) };
        let (g, h, out) = if neg(g) == 1 { (g ^ 1, h ^ 1, 1) } else { (g, h, 0) };
        if let Some(r) = self.ite_c.get(f, g, h) {
            return r ^ out;
        }
        let v = self.top(f).min(self.top(g)).min(self.top(h));
        let (f0, f1) = self.cof(f, v);
        let (g0, g1) = self.cof(g, v);
        let (h0, h1) = self.cof(h, v);
        let lo = self.ite(f0, g0, h0);
        let hi = self.ite(f1, g1, h1);
        let r = self.mk(v, lo, hi);
        self.ite_c.put(f, g, h, r);
        r ^ out
    }

    pub fn and(&mut self, f: B, g: B) -> B {
        self.ite(f, g, FALSE)
    }
    pub fn or(&mut self, f: B, g: B) -> B {
        self.ite(f, TRUE, g)
    }
    pub fn implies(&mut self, f: B, g: B) -> B {
        self.ite(f, g, TRUE)
    }
    pub fn iff(&mut self, f: B, g: B) -> B {
        self.ite(f, g, g ^ 1)
    }

    /// Intern a set of variables for quantification.
    pub fn var_set(&mut self, vars: &[u32]) -> u32 {
        let mut key = vars.to_vec();
        key.sort_unstable();
        key.dedup();
        if let Some(&id) = self.set_ids.get(&key) {
            return id;
        }
        let max = key.last().copied().unwrap_or(0) as usize;
        let mut mask = vec![false; max + 1];
        for v in &key {
            mask[*v as usize] = true;
        }
        let id = self.var_sets.len() as u32;
        self.var_sets.push(mask);
        self.set_ids.insert(key, id);
        id
    }

    /// ∃ over a set; ∀ is its dual: ∀s.f = ¬∃s.¬f, free with complement edges.
    pub fn exists(&mut self, f: B, set: u32) -> B {
        if is_const(f) {
            return f;
        }
        let n = self.nodes[idx(f)];
        let mlen = self.var_sets[set as usize].len();
        if n.var as usize >= mlen {
            return f;
        }
        if let Some(r) = self.quant_c.get(f, set, 0) {
            return r;
        }
        let c = neg(f);
        let (lo, hi) = (n.lo ^ c, n.hi ^ c);
        let quantified = self.var_sets[set as usize][n.var as usize];
        let l = self.exists(lo, set);
        let r = if quantified && l == TRUE {
            TRUE
        } else {
            let h = self.exists(hi, set);
            if quantified { self.or(l, h) } else { self.mk(n.var, l, h) }
        };
        self.quant_c.put(f, set, 0, r);
        r
    }

    pub fn forall(&mut self, f: B, set: u32) -> B {
        self.exists(f ^ 1, set) ^ 1
    }

    /// ∧ over x in `set` of ∀x.f, in one pass: the worlds where flipping any
    /// single variable of the set stays inside f. (Empty set: f.)
    ///   H(f) = ite(v, H(hi), H(lo)) ∧ (v ∈ set ? lo ∧ hi : true)
    pub fn forall_each(&mut self, f: B, set: u32) -> B {
        if is_const(f) {
            return f;
        }
        let n = self.nodes[idx(f)];
        let mlen = self.var_sets[set as usize].len();
        if n.var as usize >= mlen {
            return f;
        }
        if let Some(r) = self.quant_c.get(f, set, 2) {
            return r;
        }
        let c = neg(f);
        let (lo, hi) = (n.lo ^ c, n.hi ^ c);
        let hl = self.forall_each(lo, set);
        let hh = self.forall_each(hi, set);
        let mut r = self.mk(n.var, hl, hh);
        if self.var_sets[set as usize][n.var as usize] {
            let both = self.and(lo, hi);
            r = self.and(r, both);
        }
        self.quant_c.put(f, set, 2, r);
        r
    }

    /// f with variable `var` fixed to `val`. Only nodes above `var` are rebuilt.
    pub fn restrict(&mut self, f: B, var: u32, val: bool) -> B {
        if is_const(f) {
            return f;
        }
        let n = self.nodes[idx(f)];
        if n.var > var {
            return f;
        }
        let c = neg(f);
        if n.var == var {
            return if val { n.hi ^ c } else { n.lo ^ c };
        }
        let reg = f & !1;
        if let Some(r) = self.restrict_c.get(reg, var, val as u32) {
            return r ^ c;
        }
        let lo = self.restrict(n.lo, var, val);
        let hi = self.restrict(n.hi, var, val);
        let r = self.mk(n.var, lo, hi);
        self.restrict_c.put(reg, var, val as u32, r);
        r ^ c
    }

    /// Evaluate under a full assignment.
    pub fn eval(&self, mut f: B, assign: &[bool]) -> bool {
        let mut parity = 0;
        while !is_const(f) {
            parity ^= neg(f);
            let n = self.nodes[idx(f)];
            f = if assign[n.var as usize] { n.hi } else { n.lo };
        }
        (f ^ parity) == TRUE
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of nodes reachable from f.
    pub fn size(&self, f: B) -> usize {
        let mut seen = std::collections::HashSet::new();
        let mut st = vec![idx(f)];
        while let Some(x) = st.pop() {
            if x == 0 || !seen.insert(x) {
                continue;
            }
            let n = self.nodes[x];
            st.push(idx(n.lo));
            st.push(idx(n.hi));
        }
        seen.len()
    }

    /// Drop every node not reachable from `roots`; returns the roots renumbered.
    pub fn gc(&mut self, roots: &[B]) -> Vec<B> {
        let n = self.nodes.len();
        let mut live = vec![false; n];
        live[0] = true;
        let mut stack: Vec<usize> = roots.iter().map(|r| idx(*r)).collect();
        while let Some(i) = stack.pop() {
            if live[i] {
                continue;
            }
            live[i] = true;
            let nd = self.nodes[i];
            stack.push(idx(nd.lo));
            stack.push(idx(nd.hi));
        }
        let live_n = live.iter().filter(|x| **x).count();
        let mut map = vec![u32::MAX; n];
        let mut nodes = Vec::with_capacity(live_n);
        let mut unique = Unique::with_capacity(live_n);
        let remap = |map: &[u32], f: B| (map[idx(f)] << 1) | neg(f);
        for (i, nd) in self.nodes.iter().enumerate() {
            if !live[i] {
                continue;
            }
            let id = nodes.len() as u32;
            map[i] = id;
            if i == 0 {
                nodes.push(*nd);
                continue;
            }
            let (lo, hi) = (remap(&map, nd.lo), remap(&map, nd.hi));
            nodes.push(Node { var: nd.var, lo, hi });
            if let Err(slot) = unique.find(&nodes, nd.var, lo, hi) {
                unique.insert_at(slot, id, &nodes);
            }
        }
        self.nodes = nodes;
        self.unique = unique;
        let bits = self.ite_c.bits();
        self.ite_c.clear_resize(bits);
        self.quant_c.clear_resize(bits - 1);
        self.restrict_c.clear_resize(bits - 1);
        roots.iter().map(|r| remap(&map, *r)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(b: &Bdd, f: B, n: usize) -> Vec<bool> {
        (0..1usize << n).map(|k| b.eval(f, &(0..n).map(|i| (k >> i) & 1 == 1).collect::<Vec<_>>())).collect()
    }

    #[test]
    fn basics() {
        let mut b = Bdd::new();
        let x = b.var(0);
        let y = b.var(1);
        let xy = b.and(x, y);
        let s = b.var_set(&[0]);
        assert_eq!(b.exists(xy, s), y);
        assert_eq!(b.forall(xy, s), FALSE);
        let o = b.or(x, y);
        let nx = b.not(x);
        assert_eq!(o, b.implies(nx, y));
        assert!(b.eval(xy, &[true, true]));
        assert!(!b.eval(xy, &[true, false]));
        assert_eq!(b.restrict(xy, 0, true), y);
        assert_eq!(b.restrict(xy, 0, false), FALSE);
    }

    /// Every operation agrees with brute-force truth tables on random functions.
    #[test]
    fn random_against_truth_tables() {
        let n = 5;
        let mut b = Bdd::new();
        let mut rng: u64 = 12345;
        let mut next = || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        let mut pool: Vec<B> = (0..n as u32).map(|i| b.var(i)).collect();
        for _ in 0..400 {
            let a = pool[(next() % pool.len() as u64) as usize];
            let c = pool[(next() % pool.len() as u64) as usize];
            let d = pool[(next() % pool.len() as u64) as usize];
            let ta = table(&b, a, n);
            let tc = table(&b, c, n);
            let td = table(&b, d, n);
            let op = next() % 7;
            let (r, want): (B, Vec<bool>) = match op {
                0 => (b.and(a, c), ta.iter().zip(&tc).map(|(x, y)| *x && *y).collect()),
                1 => (b.or(a, c), ta.iter().zip(&tc).map(|(x, y)| *x || *y).collect()),
                2 => (b.not(a), ta.iter().map(|x| !x).collect()),
                3 => (b.ite(a, c, d), (0..ta.len()).map(|k| if ta[k] { tc[k] } else { td[k] }).collect()),
                6 => {
                    let k = 1 + (next() % 3) as usize;
                    let vs: Vec<u32> = (0..k).map(|_| (next() % n as u64) as u32).collect();
                    let s = b.var_set(&vs);
                    let r = b.forall_each(a, s);
                    let want = (0..ta.len()).map(|w| ta[w] && vs.iter().all(|v| ta[w & !(1 << v)] && ta[w | (1 << v)])).collect();
                    (r, want)
                }
                4 => {
                    let v = (next() % n as u64) as u32;
                    let s = b.var_set(&[v]);
                    let r = b.forall(a, s);
                    (r, (0..ta.len()).map(|k| ta[k & !(1 << v)] && ta[k | (1 << v)]).collect())
                }
                _ => {
                    let v = (next() % n as u64) as u32;
                    let val = next() % 2 == 1;
                    let r = b.restrict(a, v, val);
                    (r, (0..ta.len()).map(|k| if val { ta[k | (1 << v)] } else { ta[k & !(1 << v)] }).collect())
                }
            };
            assert_eq!(table(&b, r, n), want, "op {}", op);
            pool.push(r);
            if pool.len() > 40 {
                let keep: Vec<B> = pool.drain(pool.len() - 20..).collect();
                let renamed = b.gc(&keep);
                pool = renamed;
                for i in 0..n as u32 {
                    let v = b.var(i);
                    pool.push(v);
                }
            }
        }
    }

    #[test]
    fn gc_preserves_functions_and_canonicity() {
        let mut b = Bdd::new();
        let build = |b: &mut Bdd| {
            let vs: Vec<B> = (0..6).map(|i| b.var(i)).collect();
            let mut f = FALSE;
            for w in vs.windows(2) {
                let t = b.and(w[0], w[1]);
                f = b.or(f, t);
            }
            f
        };
        let f = build(&mut b);
        let _junk = b.iff(f, TRUE);
        let before = table(&b, f, 6);
        let r = b.gc(&[f]);
        assert_eq!(table(&b, r[0], 6), before);
        assert_eq!(build(&mut b), r[0]);
    }
}
