use {
    crate::{
        clause::{ClauseDB, ClauseId, Watch},
        config::Config,
        state::{Stat, State},
        traits::*,
        types::*,
        var::{LRB, Var, VarDB},
    },
    std::{
        fmt,
        fs::File,
        io::{BufWriter, Write},
        ops::{Index, Range, RangeFrom},
    },
};

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Debug)]
pub struct AssignStack {
    pub trail: Vec<Lit>,
    // pub conflict_weight: f64,
    asgvec: Vec<Option<bool>>,
    /// record of the number of vars assigned under a level.
    trail_lim: Vec<usize>,
    /// points to the first unpropagated var
    q_head: usize,
    var_order: VarIdHeap, // Variable Order
}

impl Default for AssignStack {
    fn default() -> Self {
        AssignStack {
            trail: Vec::new(),
            asgvec: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            var_order: VarIdHeap::new(0, 0),
        }
    }
}

/// ```
/// let x: Lbool = var_assign!(self, lit.vi());
/// ```
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.asgvec.get_unchecked($var) }
    };
}

macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => {
                #[allow(unused_unsafe)]
                // unsafe { *$asg.asgvec.get_unchecked(l.vi()) ^ (l as u8 & 1) }
                match unsafe { *$asg.asgvec.get_unchecked(l.vi()) } {
                    Some(x) if !bool::from(l) => Some(!x),
                    x => x,
                }
            }
        }
    };
}

macro_rules! set_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => unsafe {
                *$asg.asgvec.get_unchecked_mut(l.vi()) = Some(bool::from(l));
            },
        }
    };
}

#[allow(unused_unsafe)]
macro_rules! unset_assign {
    ($asg: expr, $var: expr) => {
        unsafe {
            *$asg.asgvec.get_unchecked_mut($var) = None;
        }
    };
}

impl Index<usize> for AssignStack {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        unsafe { self.trail.get_unchecked(i) }
    }
}

impl Index<Range<usize>> for AssignStack {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Lit] {
        &self.trail[r]
    }
}

impl Index<RangeFrom<usize>> for AssignStack {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Lit] {
        unsafe { self.trail.get_unchecked(r) }
    }
}

impl Instantiate for AssignStack {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> AssignStack {
        let nv = cnf.num_of_variables;
        AssignStack {
            trail: Vec::with_capacity(nv),
            // conflict_weight: 0.0,
            asgvec: vec![None; 1 + nv],
            var_order: VarIdHeap::new(nv, nv),
            .. AssignStack::default()
        }
    }
}

impl PropagatorIF for AssignStack {
    fn len(&self) -> usize {
        self.trail.len()
    }
    fn is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    fn unpropagated_index(&self) -> usize {
        self.q_head
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
    fn assigned(&self, l: Lit) -> Option<bool> {
        lit_assign!(self, l)
    }
    fn enqueue(&mut self, v: &mut Var, sig: bool, cid: ClauseId, dl: usize) -> MaybeInconsistent {
        debug_assert!(!v.is(Flag::ELIMINATED));
        match var_assign!(self, v.index) {
            None => {
                set_assign!(self, Lit::from_var(v.index, sig));
                v.assign = Some(sig);
                v.reason = cid;
                v.level = dl;
                if dl == 0 {
                    v.reason = ClauseId::default();
                    // v.activity = 0.0;
                }
                // v.polarity.update(if sig { 1.0 } else { -1.0 });
                debug_assert!(!self.trail.contains(&Lit::from_var(v.index, true)));
                debug_assert!(!self.trail.contains(&Lit::from_var(v.index, false)));
                self.trail.push(Lit::from_var(v.index, sig));
                Ok(())
            }
            Some(x) if x == sig => Ok(()),
            _ => Err(SolverError::Inconsistent),
        }
    }
    fn enqueue_null(&mut self, v: &mut Var, sig: bool) {
        debug_assert!(!v.is(Flag::ELIMINATED));
        if var_assign!(self, v.index).is_none() {
            set_assign!(self, Lit::from_var(v.index, sig));
            v.assign = Some(sig);
            v.reason = ClauseId::default();
            v.level = 0;
            // v.polarity.update(if sig { 1.0 } else { -1.0 });
            self.trail.push(Lit::from_var(v.index, sig));
        }
        // debug_assert!(self.assign[v.index] == sig);
    }
    /// propagate without checking dead clauses
    /// Note: this function assumes there's no dead clause.
    /// So Eliminator should call `garbage_collect` before me.
    fn propagate(&mut self, cdb: &mut ClauseDB, state: &mut State, vdb: &mut VarDB) -> ClauseId {
        // let ncnfl = state.stats[Stat::Conflict] + 1;
        let watcher = &mut cdb.watcher[..] as *mut [Vec<Watch>];
        while self.remains() {
            let p = self.sweep();
            let false_lit = !p;
            state.stats[Stat::Propagation] += 1;
            unsafe {
                let source = (*watcher).get_unchecked_mut(usize::from(p));
                let mut n = 0;
                'next_clause: while n < source.len() {
                    let w = source.get_unchecked_mut(n);
                    n += 1;
                    debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    let blocker_value = lit_assign!(self, w.blocker);
                    if blocker_value == Some(true) {
                        continue 'next_clause;
                    }
                    let lits = &mut cdb[w.c].lits;
                    if lits.len() == 2 {
                        if blocker_value == Some(false) {
                            // self.conflict_weight = vdb[p.vi()].record_conflict(ncnfl);
                            // state.rst.rcc.update(self.conflict_weight);
                            return w.c;
                        }
                        self.uncheck_enqueue(vdb, w.blocker, w.c);
                        continue 'next_clause;
                    }
                    debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                    let mut first = *lits.get_unchecked(0);
                    if first == false_lit {
                        first = *lits.get_unchecked(1);
                        lits.swap(0, 1);
                    }
                    let first_value = lit_assign!(self, first);
                    if first != w.blocker && first_value == Some(true) {
                        w.blocker = first;
                        continue 'next_clause;
                    }
                    for (k, lk) in lits.iter().enumerate().skip(2) {
                        if lit_assign!(self, *lk) != Some(false) {
                            (*watcher)
                                .get_unchecked_mut(usize::from(!*lk))
                                .register(first, w.c);
                            n -= 1;
                            source.detach(n);
                            lits.swap(1, k);
                            continue 'next_clause;
                        }
                    }
                    if first_value == Some(false) {
                        // self.conflict_weight = vdb[p.vi()].record_conflict(ncnfl);
                        // state.rst.rcc.update(self.conflict_weight);
                        return w.c;
                    }
                    self.uncheck_enqueue(vdb, first, w.c);
                }
            }
        }
        ClauseId::default()
    }
    fn cancel_until(&mut self, vdb: &mut VarDB, lv: usize) {
        if self.trail_lim.len() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            let v = &mut vdb[vi];
            unset_assign!(self, vi);
            v.phase = v.assign.unwrap();
            v.assign = None;
            v.reason = ClauseId::default();
            vdb.lrb_unassign(vi);
            self.var_order.insert(vdb, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }
    fn uncheck_enqueue(&mut self, vdb: &mut VarDB, l: Lit, cid: ClauseId) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be equeued");
        debug_assert!(
            self.trail_lim.is_empty() || cid != ClauseId::default(),
            "Null CLAUSE is used for uncheck_enqueue"
        );
        let dl = self.trail_lim.len();
        let vi = l.vi();
        let v = &mut vdb[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(
            var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none()
        );
        set_assign!(self, l);
        v.assign = Some(bool::from(l));
        v.level = dl;
        v.reason = cid;
        vdb.lrb_assign(vi);
        // v.polarity.update(if bool::from(l) { 1.0 } else { -1.0 });
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn uncheck_assume(&mut self, vdb: &mut VarDB, l: Lit) {
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l), format!("{:?}", l));
        self.level_up();
        let dl = self.trail_lim.len();
        let vi = l.vi();
        let v = &mut vdb[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        // debug_assert!(self.assign[vi] == l.lbool() || self.assign[vi] == BOTTOM);
        set_assign!(self, l);
        v.assign = Some(bool::from(l));
        v.level = dl;
        v.reason = ClauseId::default();
        vdb.lrb_assign(vi);
        // v.polarity.update(if bool::from(l) { 1.0 } else { -1.0 });
        self.trail.push(l);
    }
    fn select_var(&mut self, vdb: &mut VarDB) -> VarId {
        self.var_order.select_var(vdb)
    }
    fn update_order(&mut self, vdb: &mut VarDB, v: VarId) {
        self.var_order.update(vdb, v)
    }
    fn rebuild_order(&mut self, vdb: &mut VarDB) {
        self.var_order.rebuild(vdb);
    }
    #[allow(dead_code)]
    fn dump_cnf(&mut self, cdb: &ClauseDB, state: &State, vdb: &VarDB, fname: &str) {
        for v in &vdb[1..] {
            if v.is(Flag::ELIMINATED) {
                if var_assign!(self, v.index).is_some() {
                    panic!(
                        "conflicting var {} {:?}",
                        v.index,
                        var_assign!(self, v.index)
                    );
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
                    buf.write_all(format!("{} ", i32::from(*l)).as_bytes())
                        .unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in &self.trail {
                buf.write_all(format!("{} 0\n", i32::from(*x)).as_bytes())
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
    fn update(&mut self, vdb: &mut VarDB, v: VarId);
    fn insert(&mut self, vdb: &mut VarDB, vi: VarId);
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, vdb: &mut VarDB) -> VarId;
    fn rebuild(&mut self, vdb: &mut VarDB);
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
    fn update(&mut self, vdb: &mut VarDB, v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vdb, start)
        }
    }
    fn insert(&mut self, vdb: &mut VarDB, vi: VarId) {
        if self.contains(vi) {
            let i = self.idxs[vi];
            self.percolate_up(vdb, i);
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        self.idxs[0] = n;
        self.percolate_up(vdb, n);
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
    fn select_var(&mut self, vdb: &mut VarDB) -> VarId {
        loop {
            let vi = self.get_root(vdb);
            if vdb[vi].assign.is_none() && !vdb[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
    fn rebuild(&mut self, vdb: &mut VarDB) {
        self.reset();
        for vi in 1..vdb.len() {
            if vdb[vi].assign.is_none() && !vdb[vi].is(Flag::ELIMINATED) {
                self.insert(vdb, vi);
            }
        }
    }
}

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
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
    fn get_root(&mut self, vdb: &mut VarDB) -> VarId {
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
            self.percolate_down(vdb, 1);
        }
        vs
    }
    fn percolate_up(&mut self, vdb: &mut VarDB, start: usize) {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vdb.activity(vq);
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vdb.activity(vp);
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
    fn percolate_down(&mut self, vdb: &mut VarDB, start: usize) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = vdb.activity(vi);
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = vdb.activity(vl);
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al < vdb.activity(self.heap[r]) {
                    let vr = self.heap[r];
                    (r, vr, vdb.activity(vr))
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
    fn remove(&mut self, vdb: &mut VarDB, vs: VarId) {
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
            self.percolate_down(vdb, 1);
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
