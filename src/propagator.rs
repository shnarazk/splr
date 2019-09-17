use crate::clause::{ClauseDB, Watch};
use crate::state::{Stat, State};
use crate::traits::{ClauseDBIF, FlagIF, LitIF, PropagatorIF, WatchDBIF};
use crate::types::*;
use crate::var::{Var, VarDB};
use std::fmt;
use std::fs::File;
use std::io::{BufWriter, Write};

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Debug)]
pub struct AssignStack {
    pub trail: Vec<Lit>,
    assign: Vec<Lbool>,
    asgvec: Vec<u64>,
    trail_lim: Vec<usize>,
    q_head: usize,
    var_order: VarIdHeap, // Variable Order
}

/// ```
/// let x: Lbool = var_assign!(self.assign, lit.vi());
/// ```
macro_rules! var_assign {
    ($vec: expr, $var: expr) => {
        match ($vec, $var) {
            (v, vi) => {
                let a = &v[vi >> 5];
                let w = 2 * (vi % 32);
                ((*a >> w) & 3) as u8
            }
        }
    }
}

macro_rules! lit_assign {
    ($vec: expr, $lit: expr) => {
        match ($vec, $lit) {
            (v, l) => {
                let vi = l.vi();
                let a = &v[vi >> 5];
                let w = (vi % 32) << 1;
                match (((*a >> w) & 3) as u8) ^ ((l & 1) as u8) {
                    TRUE => TRUE,
                    FALSE => FALSE,
                    _ => BOTTOM,
                }
            }
        }
    }
}

macro_rules! set_assign {
    ($vec: expr, $lit: expr) => {
        match ($vec, $lit) {
            (v, l) => {
                let vi = l.vi();
                let a = &mut v[vi >> 5];
                let w = (vi % 32) << 1;
                let b = l.lbool();
                *a &= !(3 << w);
                *a |= (b as u64) << w;
            }
        }
    }
}
macro_rules! unset_assign {
    ($vec: expr, $var: expr) => {
        match ($vec, $var) {
            (v, vi) => {
                let a = &mut v[vi >> 5];
                let w = (vi % 32) << 1;
                // 0 for TRUE, 1 for FALSE, 2 for BOTTOM
                *a &= !(1 << w);
                *a |= 2 << w;
            }
        }
    }
}

impl PropagatorIF for AssignStack {
    fn new(n: usize) -> AssignStack {
        AssignStack {
            trail: Vec::with_capacity(n),
            assign: vec![BOTTOM; n + 1],
            asgvec: vec![0xaaaa_aaaa_aaaa_aaaa; 1 + n / 32],
            trail_lim: Vec::new(),
            q_head: 0,
            var_order: VarIdHeap::new(n, n),
        }
    }
    fn len(&self) -> usize {
        self.trail.len()
    }
    fn is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    fn level(&self) -> usize {
        self.trail_lim.len()
    }
    fn is_zero(&self) -> bool {
        self.trail_lim.is_empty()
    }
    fn num_at(&self, n: usize) -> usize {
        self.trail_lim[n]
    }
    fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    /// - to set `lit` to TRUE
    /// ```
    /// let v = l.vi();
    /// let a = &mut self.assign[v >> 5];
    /// let w = 2 * v % 32;
    /// let b = lit.lbool();
    /// *a &= !(3 << w);
    /// *a |= (b as u64) << w;
    /// ```
    fn assigned(&self, l: Lit) -> Lbool {
        let x = unsafe { self.assign.get_unchecked(l.vi()) ^ ((l & 1) as u8) };
        let y = lit_assign!(&self.asgvec, l);
        assert!(x == y || (1 < x && 1 < y), format!("assign: {}, asgvec: {}", x, y));
        unsafe { self.assign.get_unchecked(l.vi()) ^ ((l & 1) as u8) }
        // let vi = l.vi();
        // (((self.assign[vi >> 5] >> (2 * (vi % 32))) & 3) as u8) ^ ((l & 1) as u8)
        // lit_assign!(&self.assign, l)
    }
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> MaybeInconsistent {
        debug_assert!(!v.is(Flag::ELIMINATED));
        let val = self.assign[v.index];
        assert_eq!(val, var_assign!(&self.asgvec, v.index));
        if val == BOTTOM {
            self.assign[v.index] = sig;
            set_assign!(&mut self.asgvec, Lit::from_var(v.index, sig));
            assert_eq!(self.assign[v.index], var_assign!(&self.asgvec, v.index));
            v.assign = sig;
            v.reason = cid;
            v.level = dl;
            if dl == 0 {
                v.reason = NULL_CLAUSE;
                v.activity = 0.0;
            }
            debug_assert!(!self.trail.contains(&Lit::from_var(v.index, TRUE)));
            debug_assert!(!self.trail.contains(&Lit::from_var(v.index, FALSE)));
            self.trail.push(Lit::from_var(v.index, sig));
            Ok(())
        } else if val == sig {
            Ok(())
        } else {
            Err(SolverError::Inconsistent)
        }
    }
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool) {
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(sig != BOTTOM);
        let val = self.assign[v.index];
        assert_eq!(val, var_assign!(&self.asgvec, v.index));
        if val == BOTTOM {
            self.assign[v.index] = sig;
            set_assign!(&mut self.asgvec, Lit::from_var(v.index, sig));
            assert_eq!(self.assign[v.index], var_assign!(&self.asgvec, v.index));
            v.assign = sig;
            v.reason = NULL_CLAUSE;
            v.level = 0;
            self.trail.push(Lit::from_var(v.index, sig));
        }
        debug_assert!(self.assign[v.index] == sig);
    }
    /// propagate without checking dead clauses
    /// Note: this function assumes there's no dead clause.
    /// So Eliminator should call `garbage_collect` before me.
    fn propagate(&mut self, cdb: &mut ClauseDB, state: &mut State, vars: &mut VarDB) -> ClauseId {
        let watcher = &mut cdb.watcher[..] as *mut [Vec<Watch>];
        while self.remains() {
            let p: usize = self.sweep() as usize;
            let false_lit = (p as Lit).negate();
            state.stats[Stat::Propagation] += 1;
            unsafe {
                let source = (*watcher).get_unchecked_mut(p);
                let mut n = 0;
                'next_clause: while n < source.len() {
                    let w = source.get_unchecked_mut(n);
                    n += 1;
                    debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    let blocker_value = self.assigned(w.blocker);
                    if blocker_value == TRUE {
                        continue 'next_clause;
                    }
                    let lits = &mut cdb[w.c].lits;
                    if lits.len() == 2 {
                        match blocker_value {
                            FALSE => {
                                self.catchup();
                                return w.c;
                            }
                            _ => {
                                self.uncheck_enqueue(vars, w.blocker, w.c);
                                continue 'next_clause;
                            }
                        }
                    }
                    debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                    let mut first = *lits.get_unchecked(0);
                    if first == false_lit {
                        first = *lits.get_unchecked(1);
                        *lits.get_unchecked_mut(0) = first;
                        *lits.get_unchecked_mut(1) = false_lit;
                    }
                    let first_value = self.assigned(first);
                    // If 0th watch is true, then clause is already satisfied.
                    if first != w.blocker && first_value == TRUE {
                        w.blocker = first;
                        continue 'next_clause;
                    }
                    for (k, lk) in lits.iter().enumerate().skip(2) {
                        // below is equivalent to 'assigned(*lk) != FALSE'
                        // if (((lk & 1) as u8) ^ self.assign.get_unchecked(lk.vi())) != 0 {
                        if self.assigned(*lk) != FALSE {
                            (*watcher)
                                .get_unchecked_mut(lk.negate() as usize)
                                .register(first, w.c);
                            n -= 1;
                            source.detach(n);
                            *lits.get_unchecked_mut(1) = *lk;
                            *lits.get_unchecked_mut(k) = false_lit;
                            continue 'next_clause;
                        }
                    }
                    if first_value == FALSE {
                        self.catchup();
                        return w.c;
                    } else {
                        self.uncheck_enqueue(vars, first, w.c);
                    }
                }
            }
        }
        NULL_CLAUSE
    }
    fn cancel_until(&mut self, vars: &mut VarDB, lv: usize) {
        if self.trail_lim.len() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            let v = &mut vars[vi];
            v.phase = self.assign[vi];
            assert_eq!(self.assign[v.index], var_assign!(&self.asgvec, v.index));
            self.assign[vi] = BOTTOM;
            unset_assign!(&mut self.asgvec, vi);
            assert_eq!(self.assign[v.index], var_assign!(&self.asgvec, v.index));
            v.assign = BOTTOM;
            v.reason = NULL_CLAUSE;
            self.var_order.insert(vars, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }
    fn uncheck_enqueue(&mut self, vars: &mut VarDB, l: Lit, cid: ClauseId) {
        debug_assert!(l != 0, "Null literal is about to be equeued");
        debug_assert!(
            self.trail_lim.is_empty() || cid != 0,
            "Null CLAUSE is used for uncheck_enqueue"
        );
        let dl = self.trail_lim.len();
        let vi = l.vi();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(self.assign[vi] == l.lbool() || self.assign[vi] == BOTTOM);
        self.assign[vi] = l.lbool();
        set_assign!(&mut self.asgvec, l);
        assert_eq!(self.assign[v.index], var_assign!(&self.asgvec, v.index));
        v.assign = l.lbool();
        v.level = dl;
        v.reason = cid;
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&l.negate()));
        self.trail.push(l);
    }
    fn uncheck_assume(&mut self, vars: &mut VarDB, l: Lit) {
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&l.negate()));
        self.level_up();
        let dl = self.trail_lim.len();
        let vi = l.vi();
        let v = &mut vars[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(self.assign[vi] == l.lbool() || self.assign[vi] == BOTTOM);
        self.assign[vi] = l.lbool();
        set_assign!(&mut self.asgvec, l);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = NULL_CLAUSE;
        self.trail.push(l);
    }
    fn select_var(&mut self, vars: &VarDB) -> VarId {
        self.var_order.select_var(vars)
    }
    fn update_order(&mut self, vec: &VarDB, v: VarId) {
        self.var_order.update(vec, v)
    }
    #[allow(dead_code)]
    fn dump_cnf(&mut self, cdb: &ClauseDB, state: &State, vars: &VarDB, fname: &str) {
        for v in &vars[1..] {
            if v.is(Flag::ELIMINATED) {
                if self.assign[v.index] < BOTTOM {
                    panic!("conflicting var {} {}", v.index, self.assign[v.index]);
                } else {
                    println!("eliminate var {}", v.index);
                }
            }
        }
        if let Ok(out) = File::create(&fname) {
            let mut buf = BufWriter::new(out);
            let nv = self.len();
            let nc: usize = cdb.len() - 1;
            buf.write_all(format!("p cnf {} {}\n", state.num_vars, nc + nv).as_bytes())
                .unwrap();
            for c in &cdb[1..] {
                for l in &c.lits {
                    buf.write_all(format!("{} ", l.to_i32()).as_bytes())
                        .unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in &self.trail {
                buf.write_all(format!("{} 0\n", x.to_i32()).as_bytes())
                    .unwrap();
            }
        }
    }
}

impl AssignStack {
    fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    fn sweep(&mut self) -> Lit {
        let lit = self.trail[self.q_head];
        self.q_head += 1;
        lit
    }
    fn catchup(&mut self) {
        self.q_head = self.trail.len();
    }
}

/// Heap of VarId, based on var activity
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarIdHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn update(&mut self, vec: &VarDB, v: VarId);
    fn insert(&mut self, vec: &VarDB, vi: VarId);
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, vars: &VarDB) -> VarId;
    fn rebuild(&mut self, vars: &VarDB);
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
    fn update(&mut self, vec: &VarDB, v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vec, start)
        }
    }
    fn insert(&mut self, vec: &VarDB, vi: VarId) {
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
    fn select_var(&mut self, vars: &VarDB) -> VarId {
        loop {
            let vi = self.get_root(vars);
            if BOTTOM <= vars[vi].assign && !vars[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
    fn rebuild(&mut self, vars: &VarDB) {
        self.reset();
        for v in &vars[1..] {
            if BOTTOM <= v.assign && !v.is(Flag::ELIMINATED) {
                self.insert(vars, v.index);
            }
        }
    }
}

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| l.to_i32()).collect::<Vec<i32>>();
        let len = self.level();
        let c = |i| {
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
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn get_root(&mut self, vars: &VarDB) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vars, 1);
        }
        vs
    }
    fn percolate_up(&mut self, vars: &VarDB, start: usize) {
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
    fn percolate_down(&mut self, vars: &VarDB, start: usize) {
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
    #[allow(dead_code)]
    fn remove(&mut self, vars: &VarDB, vs: VarId) {
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
            self.percolate_down(&vars, 1);
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
