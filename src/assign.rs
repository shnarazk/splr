use crate::clause::{ClauseDB, ClauseKind};
use crate::config::SolverConfiguration;
use crate::eliminator::Eliminator;
use crate::traits::*;
use crate::types::*;
use crate::var::{Var, VarIdHeap};
use std::fs::File;
use std::io::{BufWriter, Write};

pub struct AssignStack {
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
}

impl AssignStack {
    pub fn new(n: usize) -> AssignStack {
        AssignStack {
            trail: Vec::with_capacity(n),
            trail_lim: Vec::new(),
            q_head: 0,
        }
    }
    #[inline(always)]
    pub fn push(&mut self, l: Lit) {
        self.trail.push(l);
    }
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.trail.len()
    }
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    #[inline(always)]
    pub fn level(&self) -> usize {
        self.trail_lim.len()
    }
    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.trail_lim.is_empty()
    }
    #[inline(always)]
    pub fn num_at(&self, n: usize) -> usize {
        self.trail_lim[n]
    }
    #[inline(always)]
    pub fn sweep(&mut self) -> Lit {
        let lit = self.trail[self.q_head];
        self.q_head += 1;
        lit
    }
    #[inline(always)]
    pub fn catchup(&mut self) {
        self.q_head = self.trail.len();
    }
    #[inline(always)]
    pub fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    #[inline(always)]
    pub fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    /// returns `false` if an conflict occures.
    pub fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> bool {
        let val = v.assign;
        if val == BOTTOM {
            debug_assert!(!v.eliminated);
            v.assign = sig;
            // if dl == 0 && cid != NULL_CLAUSE {
            //     println!("enqueue {}", cid.fmt());
            // }
            v.reason = cid;
            v.level = dl;
            if dl == 0 {
                // if !v.enqueued {
                //     self.eliminator.var_queue.push(l.vi());
                //     v.enqueued = true;
                // }
                v.reason = NULL_CLAUSE;
                v.activity = 0.0;
            }
            // if dl == 0 {
            //     self.var_order.remove(&self.vars, l.vi());
            // }
            // debug_assert!(!self.trail.contains(&l));
            // debug_assert!(!self.trail.contains(&l.negate()));
            self.trail.push(v.index.lit(sig));
            true
        } else {
            val == sig
        }
    }
    /// returns `false` if an conflict occures.
    pub fn enqueue_null(&mut self, v: &mut Var, sig: Lbool, dl: usize) -> bool {
        let val = v.assign;
        if val == BOTTOM {
            debug_assert!(!v.eliminated);
            v.assign = sig;
            v.reason = NULL_CLAUSE;
            v.level = dl;
            if dl == 0 {
                v.activity = 0.0;
            }
            self.trail.push(v.index.lit(sig));
            true
        } else {
            val == sig
        }
    }

    pub fn cancel_until(&mut self, vars: &mut [Var], var_order: &mut VarIdHeap, lv: usize) {
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
            if v.reason != NULL_CLAUSE {
                v.reason = NULL_CLAUSE;
            }
            var_order.insert(vars, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }
    pub fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId) {
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
    pub fn uncheck_assume(&mut self, vars: &mut [Var], elim: &mut Eliminator, l: Lit) {
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
    fn dump_cnf(
        &mut self,
        config: &SolverConfiguration,
        cps: &ClauseDB,
        vars: &[Var],
        fname: &str,
    ) {
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
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ];
            for kind in &kinds {
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
