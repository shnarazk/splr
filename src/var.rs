use crate::clause::{Clause, ClauseFlag};
use crate::eliminator::Eliminator;
use crate::traits::*;
use crate::types::*;
use std::fmt;

const VAR_ACTIVITY_MAX: f64 = 1e240;
const VAR_ACTIVITY_SCALE1: f64 = 1e-80;
const VAR_ACTIVITY_SCALE2: f64 = 1e-10;

/// Struct for a variable.
pub struct Var {
    pub index: usize,
    pub assign: Lbool,
    pub phase: Lbool,
    pub reason: ClauseId,
    pub level: usize,
    pub activity: f64,
    /// For elimination
    pub touched: bool,
    /// For elimination
    pub eliminated: bool,
    pub check_sve_at: usize,
    pub pos_occurs: Vec<ClauseId>,
    pub neg_occurs: Vec<ClauseId>,
    pub enqueued: bool,
}

/// is the dummy var index.
#[allow(dead_code)]
const NULL_VAR: VarId = 0;

impl VarIF for Var {
    fn new(i: usize) -> Var {
        Var {
            index: i,
            assign: BOTTOM,
            phase: BOTTOM,
            reason: NULL_CLAUSE,
            level: 0,
            activity: 0.0,
            touched: false,
            eliminated: false,
            check_sve_at: 0,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            enqueued: false,
        }
    }
    fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            let mut v = Var::new(i);
            v.activity = (n - i) as f64;
            vec.push(v);
        }
        vec
    }
}

impl VarDBIF for [Var] {
    fn assigned(&self, l: Lit) -> Lbool {
        unsafe { self.get_unchecked(l.vi()).assign ^ ((l & 1) as u8) }
    }
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool {
        let lits = &c.lits;
        debug_assert!(1 < lits.len());
        let l0 = lits[0];
        self.assigned(l0) == LTRUE && self[l0.vi()].reason == cid
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        false
    }
    #[inline(always)]
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize {
        let key = keys[0] + 1;
        let mut cnt = 0;
        for l in vec {
            let lv = self[l.vi()].level;
            if keys[lv] != key {
                keys[lv] = key;
                cnt += 1;
            }
        }
        keys[0] = key;
        cnt
    }
    fn attach_clause(
        &mut self,
        elim: &mut Eliminator,
        cid: ClauseId,
        ch: &mut Clause,
        enqueue: bool,
    ) {
        if !elim.in_use {
            return;
        }
        for l in &ch.lits {
            let mut v = &mut self[l.vi()];
            v.touched = true;
            if !v.eliminated {
                if l.positive() {
                    v.pos_occurs.push(cid);
                } else {
                    v.neg_occurs.push(cid);
                }
            }
        }
        if enqueue {
            elim.enqueue_clause(cid, ch);
        }
    }
    fn detach_clause(&mut self, elim: &mut Eliminator, cid: ClauseId, ch: &Clause) {
        debug_assert!(ch.get_flag(ClauseFlag::Dead));
        if elim.in_use {
            for l in &ch.lits {
                let v = &mut self[l.vi()];
                if !v.eliminated {
                    if l.positive() {
                        v.pos_occurs.retain(|&cj| cid != cj);
                    } else {
                        v.neg_occurs.retain(|&cj| cid != cj);
                    }
                    elim.enqueue_var(v);
                }
            }
        }
    }
    fn bump_activity(&mut self, inc: &mut f64, vi: VarId, _d: f64) {
        let v = &mut self[vi];
        // v.activity = (v.activity + d) / 2.0;
        let a = v.activity + *inc;
        v.activity = a;
        if VAR_ACTIVITY_MAX < a {
            for v in &mut self[1..] {
                v.activity *= VAR_ACTIVITY_SCALE1;
            }
            *inc *= VAR_ACTIVITY_SCALE2;
        }
    }
}

/// heap of VarId
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - idxs[0] contains the number of alive elements
///   `indx` holds positions. So the unused field 0 can hold the last position as a special case.
pub struct VarIdHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
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
            if vars[vi].assign == BOTTOM && !vars[vi].eliminated {
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
            if v.assign == BOTTOM && !v.eliminated {
                self.insert(vars, v.index);
            }
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

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if flag { mes } else { "" };
        write!(
            f,
            "V{}({} at {} by {} {}{})",
            self.index,
            self.assign,
            self.level,
            self.reason.format(),
            st(self.touched, ", touched"),
            st(self.touched, ", eliminated"),
        )
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
