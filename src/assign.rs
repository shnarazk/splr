use crate::clause::ClauseDB;
use crate::config::Config;
use crate::traits::{AssignIF, FlagIF, LitIF};
use crate::types::*;
use crate::var::Var;
use std::fmt;
use std::fs::File;
use std::io::{BufWriter, Write};

pub struct AssignStack {
    pub trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    q_head: usize,
    var_order: VarIdHeap, // Variable Order
}

impl AssignIF for AssignStack {
    fn new(n: usize) -> AssignStack {
        AssignStack {
            trail: Vec::with_capacity(n),
            trail_lim: Vec::new(),
            q_head: 0,
            var_order: VarIdHeap::new(n, n),
        }
    }
    #[inline(always)]
    fn len(&self) -> usize {
        self.trail.len()
    }
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    #[inline(always)]
    fn level(&self) -> usize {
        self.trail_lim.len()
    }
    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.trail_lim.is_empty()
    }
    #[inline(always)]
    fn num_at(&self, n: usize) -> usize {
        self.trail_lim[n]
    }
    #[inline(always)]
    fn sweep(&mut self) -> Lit {
        let lit = self.trail[self.q_head];
        self.q_head += 1;
        lit
    }
    #[inline(always)]
    fn catchup(&mut self) {
        self.q_head = self.trail.len();
    }
    #[inline(always)]
    fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    #[inline(always)]
    fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    /// returns `false` if an conflict occures.
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> bool {
        debug_assert!(!v.is(Flag::EliminatedVar));
        let val = v.assign;
        if val == BOTTOM {
            v.assign = sig;
            v.reason = cid;
            v.level = dl;
            if dl == 0 {
                v.reason = NULL_CLAUSE;
                v.activity = 0.0;
            }
            debug_assert!(!self.trail.contains(&Lit::from_var(v.index, LTRUE)));
            debug_assert!(!self.trail.contains(&Lit::from_var(v.index, LFALSE)));
            self.trail.push(Lit::from_var(v.index, sig));
            true
        } else {
            val == sig
        }
    }
    /// returns `false` if an conflict occures.
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool, dl: usize) -> bool {
        debug_assert!(!v.is(Flag::EliminatedVar));
        debug_assert!(sig != BOTTOM);
        let val = v.assign;
        if val == BOTTOM {
            v.assign = sig;
            v.reason = NULL_CLAUSE;
            v.level = dl;
            self.trail.push(Lit::from_var(v.index, sig));
            true
        } else {
            val == sig
        }
    }
    fn cancel_until(&mut self, vars: &mut [Var], lv: usize) {
        if self.trail_lim.len() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            let v = &mut vars[vi];
            v.phase = v.assign;
            v.assign = BOTTOM;
            v.reason = NULL_CLAUSE;
            self.var_order.insert(vars, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }
    fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId) {
        debug_assert!(l != 0, "Null literal is about to be equeued");
        debug_assert!(
            self.trail_lim.is_empty() || cid != 0,
            "Null CLAUSE is used for uncheck_enqueue"
        );
        let dl = self.trail_lim.len();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.is(Flag::EliminatedVar));
        debug_assert!(v.assign == l.lbool() || v.assign == BOTTOM);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = cid;
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&l.negate()));
        self.trail.push(l);
    }
    fn uncheck_assume(&mut self, vars: &mut [Var], l: Lit) {
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&l.negate()));
        self.trail_lim.push(self.trail.len());
        let dl = self.trail_lim.len();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.is(Flag::EliminatedVar));
        debug_assert!(v.assign == l.lbool() || v.assign == BOTTOM);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = NULL_CLAUSE;
        self.trail.push(l);
    }
    #[allow(dead_code)]
    fn dump_cnf(&mut self, cdb: &ClauseDB, config: &Config, vars: &[Var], fname: &str) {
        for v in vars {
            if v.is(Flag::EliminatedVar) {
                if v.assign != BOTTOM {
                    panic!("conflicting var {} {}", v.index, v.assign);
                } else {
                    println!("eliminate var {}", v.index);
                }
            }
        }
        if let Ok(out) = File::create(&fname) {
            let mut buf = BufWriter::new(out);
            let nv = self.len();
            let nc: usize = cdb.clause.len() - 1;
            buf.write_all(format!("p cnf {} {}\n", config.num_vars, nc + nv).as_bytes())
                .unwrap();
            for c in &cdb.clause[1..] {
                for l in &c.lits {
                    buf.write_all(format!("{} ", l.int()).as_bytes()).unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in &self.trail {
                buf.write_all(format!("{} 0\n", x.int()).as_bytes())
                    .unwrap();
            }
        }
    }
    fn rebuild_order(&mut self, vars: &[Var]) {
        self.var_order.rebuild(vars)
    }
    fn select_var(&mut self, vars: &[Var]) -> VarId {
        self.var_order.select_var(vars)
    }
    fn update_order(&mut self, vec: &[Var], v: VarId) {
        self.var_order.update(vec, v)
    }
}

/// heap of VarId
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - idxs[0] contains the number of alive elements
///   `indx` is positions. So the unused field 0 can hold the last position as a special case.
pub struct VarIdHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn update(&mut self, vec: &[Var], v: VarId);
    fn insert(&mut self, vec: &[Var], vi: VarId);
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, vars: &[Var]) -> VarId;
    fn rebuild(&mut self, vars: &[Var]);
}

impl VarOrderIF for VarIdHeap {
    fn new(n: usize, init: usize) -> VarIdHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..=n {
            heap.push(i);
            idxs.push(i);
        }
        idxs[0] = init;
        VarIdHeap { heap, idxs }
    }
    /// renamed from incrementHeap, updateVO
    fn update(&mut self, vec: &[Var], v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vec, start)
        }
    }
    /// renamed from undoVO
    fn insert(&mut self, vec: &[Var], vi: VarId) {
        if self.contains(vi) {
            let i = self.idxs[vi];
            self.percolate_up(&vec, i);
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        self.idxs[0] = n;
        self.percolate_up(&vec, n);
    }
    fn clear(&mut self) {
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self, vars: &[Var]) -> VarId {
        loop {
            let vi = self.get_root(vars);
            if vars[vi].assign == BOTTOM && !vars[vi].is(Flag::EliminatedVar) {
                // if self.trail.contains(&vi.lit(LTRUE)) || self.trail.contains(&vi.lit(LFALSE)) {
                //     panic!("@ level {}, select_var vi {} v {:?}", self.trail_lim.len(), vi, self.vars[vi]);
                // }
                return vi;
            }
        }
    }
    fn rebuild(&mut self, vars: &[Var]) {
        // debug_assert_eq!(self.decision_level(), 0);
        self.reset();
        for v in &vars[1..] {
            if v.assign == BOTTOM && !v.is(Flag::EliminatedVar) {
                self.insert(vars, v.index);
            }
        }
    }
}

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>();
        let len = self.level();
        let c = |i|
        {
            let a = self.num_at(i);
            match i {
                0 => (0, &v[0..a]),
                x if x == len - 1 => (i + 1, &v[a..]),
                x => (x + 1, &v[a..self.num_at(x + 1)]),
            }
        };
        if 0 < len {
            write!(f, "{:?}", (0..len).map(c).collect::<Vec<(usize, &[i32])>>())
        } else {
            write!(f, "# - trail[  0]  [0{:?}]", &v)
        }
    }
}

impl VarIdHeap {
    /// renamed from inHeap
    #[inline(always)]
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    /// renamed from getHeapDown
    fn get_root(&mut self, vars: &[Var]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        // self.var_order.check(&format!("root 1 :[({}, {}) ({}, {})]", s, vs, n, vn));
        // println!("n {} vn {}", n, vn);
        // if vn == 0 {
        //     println!("n {} vn {}", n, vn);
        // }
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vars, 1);
        }
        // self.var_order.check("root 2");
        // chect the validness of the selected var
        // let mut cnt = 0;
        // let mut best = vs;
        // for v in &vars[1..] {
        //     if v.assign == BOTTOM && vars[best].activity < v.activity {
        //         best = v.index;
        //         cnt += 1;
        //     }
        // }
        // if best != vs {
        //     println!("best {}@{}/{} root {} ({})", best, self.idxs[best], self.idxs[0], vs, cnt);
        // }
        vs
    }
    fn percolate_up(&mut self, vars: &[Var], start: usize) {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vars[vq].activity;
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vars[vp].activity;
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.heap[q] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vp] = q;
                    q = p;
                } else {
                    self.heap[q] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vq] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, vars: &[Var], start: usize) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = vars[vi].activity;
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = vars[vl].activity;
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al < vars[self.heap[r]].activity {
                    let vr = self.heap[r];
                    (r, vr, vars[vr].activity)
                } else {
                    (l, vl, al)
                };
                if ai < ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = target;
                } else {
                    self.heap[i] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.idxs[vi] = i;
                    return;
                }
            } else {
                self.heap[i] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.idxs[vi] = i;
                return;
            }
        }
    }
    #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1]
    }
    /// renamed from getHeapDown
    #[allow(dead_code)]
    fn remove(&mut self, vec: &[Var], vs: VarId) {
        let s = self.idxs[vs];
        let n = self.idxs[0];
        if n < s {
            return;
        }
        let vn = self.heap[n];
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vec, 1);
        }
    }
    #[allow(dead_code)]
    fn check(&self, s: &str) {
        let h = &mut self.heap.clone()[1..];
        let d = &mut self.idxs.clone()[1..];
        h.sort();
        d.sort();
        for i in 0..h.len() {
            if h[i] != i + 1 {
                panic!("heap {} {} {:?}", i, h[i], h);
            }
            if d[i] != i + 1 {
                panic!("idxs {} {} {:?}", i, d[i], d);
            }
        }
        println!(" - pass var_order test at {}", s);
    }
}

impl fmt::Display for VarIdHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - seek pointer - nth -> var: {:?}\n - var -> nth: {:?}",
            self.heap, self.idxs,
        )
    }
}
