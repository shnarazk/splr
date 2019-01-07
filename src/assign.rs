use crate::clause::{ClauseDB, ClauseKind};
use crate::config::SolverConfig;
use crate::eliminator::Eliminator;
use crate::traits::*;
use crate::types::*;
use crate::var::{Var, VarIdHeap};
use std::fs::File;
use std::io::{BufWriter, Write};

pub struct AssignStack {
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    q_head: usize,
}

impl AssignIF for AssignStack {
    fn new(n: usize) -> AssignStack {
        AssignStack {
            trail: Vec::with_capacity(n),
            trail_lim: Vec::new(),
            q_head: 0,
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
        let val = v.assign;
        if val == BOTTOM {
            debug_assert!(!v.eliminated);
            v.assign = sig;
            v.reason = cid;
            v.level = dl;
            if dl == 0 {
                v.reason = NULL_CLAUSE;
                v.activity = 0.0;
            }
            // debug_assert!(!self.trail.contains(&l));
            // debug_assert!(!self.trail.contains(&l.negate()));
            self.trail.push(v.index.lit(sig));
            true
        } else {
            val == sig
        }
    }
    /// returns `false` if an conflict occures.
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool, dl: usize) -> bool {
        let val = v.assign;
        if val == BOTTOM {
            debug_assert!(!v.eliminated);
            v.assign = sig;
            v.reason = NULL_CLAUSE;
            v.level = dl;
            self.trail.push(v.index.lit(sig));
            true
        } else {
            val == sig
        }
    }

    fn cancel_until(&mut self, vars: &mut [Var], var_order: &mut VarIdHeap, lv: usize) {
        if self.trail_lim.len() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            // println!("cancel_until {}", l.int());
            let vi = l.vi();
            let v = &mut vars[vi];
            v.phase = v.assign;
            v.assign = BOTTOM;
            v.reason = NULL_CLAUSE;
            var_order.insert(vars, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }
    fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId) {
        // println!("uncheck_enqueue {}", l.int());
        debug_assert!(l != 0, "Null literal is about to be equeued");
        debug_assert!(
            self.trail_lim.is_empty() || cid != 0,
            "Null CLAUSE is used for uncheck_enqueue"
        );
        let dl = self.trail_lim.len();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.eliminated);
        debug_assert!(v.assign == l.lbool() || v.assign == BOTTOM);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = cid;
        // if dl == 0 {
        //     eliminator.enqueue_var(v);
        // }
        // debug_assert!(!self.trail.contains(&l));
        // debug_assert!(!self.trail.contains(&l.negate()));
        self.trail.push(l);
    }
    fn uncheck_assume(&mut self, vars: &mut [Var], elim: &mut Eliminator, l: Lit) {
        // println!("uncheck_assume {}", l.int());
        self.trail_lim.push(self.trail.len());
        let dl = self.trail_lim.len();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.eliminated);
        debug_assert!(v.assign == l.lbool() || v.assign == BOTTOM);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = NULL_CLAUSE;
        if dl == 0 {
            elim.enqueue_var(v);
        }
        // debug_assert!(!trail.contains(&l));
        // debug_assert!(!trail.contains(&l.negate()));
        self.trail.push(l);
    }
    #[allow(dead_code)]
    fn dump_cnf(&mut self, config: &SolverConfig, cps: &ClauseDB, vars: &[Var], fname: &str) {
        for v in vars {
            if v.eliminated {
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
            let nc: usize = cps.iter().map(|p| p.head.len() - 1).sum();
            buf.write_all(format!("p cnf {} {}\n", config.num_vars, nc + nv).as_bytes())
                .unwrap();
            for kind in &[
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ] {
                for c in cps[*kind as usize].head.iter().skip(1) {
                    for l in &c.lits {
                        buf.write_all(format!("{} ", l.int()).as_bytes()).unwrap();
                    }
                    buf.write_all(b"0\n").unwrap();
                }
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in &self.trail {
                buf.write_all(format!("{} 0\n", x.int()).as_bytes())
                    .unwrap();
            }
        }
    }
}
