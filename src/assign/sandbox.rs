/// This is a boolean constraint propagation sandbox not to update var and clause rewards
use {
    super::AssignStack,
    crate::{
        cdb::{ClauseDBIF, WatchDBIF},
        types::*,
    },
};

macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l =>
            {
                #[allow(unused_unsafe)]
                match unsafe { *$asg.assign.get_unchecked(l.vi()) } {
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
                let vi = l.vi();
                *$asg.assign.get_unchecked_mut(vi) = Some(bool::from(l));
                #[cfg(feature = "explore_timestamp")]
                {
                    $asg.var.get_unchecked_mut(vi).assign_timestamp = $asg.num_conflict;
                }
            },
        }
    };
}

macro_rules! unset_assign {
    ($asg: expr, $var: expr) => {
        unsafe {
            *$asg.assign.get_unchecked_mut($var) = None;
        }
    };
}

pub fn sandboxed_propagate<C>(asg: &mut AssignStack, cdb: &mut C) -> ClauseId
where
    C: ClauseDBIF,
{
    let bin_watcher = cdb.bin_watcher_lists() as *const [Vec<Watch>];
    let watcher = cdb.watcher_lists_mut() as *mut [Vec<Watch>];
    unsafe {
        while let Some(p) = asg.trail.get(asg.q_head) {
            asg.q_head += 1;
            let sweeping = usize::from(*p);
            let false_lit = !*p;
            // we have to drop `p` here to use asg as a mutable reference again later.

            //
            //## binary loop
            //
            let bin_source = (*bin_watcher).get_unchecked(sweeping);
            for w in bin_source.iter() {
                debug_assert!(!cdb[w.c].is(Flag::DEAD));
                debug_assert!(!asg.var[w.blocker.vi()].is(Flag::ELIMINATED));
                debug_assert_ne!(w.blocker, false_lit);
                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[w.c].lits.len(), 2);
                match lit_assign!(asg, w.blocker) {
                    Some(true) => (),
                    Some(false) => {
                        asg.last_conflict = false_lit.vi();
                        asg.num_conflict += 1;
                        return w.c;
                    }
                    None => {
                        asg.sandboxed_assign_by_implication(
                            w.blocker,
                            AssignReason::Implication(w.c, false_lit),
                            asg.level[false_lit.vi()],
                        );
                    }
                }
            }
            //
            //## normal clause loop
            //
            let source = (*watcher).get_unchecked_mut(sweeping);
            let mut n = 0;
            'next_clause: while n < source.len() {
                let mut w = source.get_unchecked_mut(n);
                n += 1;
                let blocker_value = lit_assign!(asg, w.blocker);
                if blocker_value == Some(true) {
                    continue 'next_clause;
                }
                // debug_assert!(!cdb[w.c].is(Flag::DEAD));
                let Clause {
                    ref mut lits,
                    ref mut search_from,
                    ..
                } = cdb[w.c];
                debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                let mut first = lits[0];
                if first == false_lit {
                    first = lits[1];
                    lits.swap(0, 1);
                }
                let first_value = lit_assign!(asg, first);
                if first != w.blocker && first_value == Some(true) {
                    w.blocker = first;
                    continue 'next_clause;
                }
                //
                //## Search an un-falsified literal
                //
                #[cfg(feature = "boundary_check")]
                assert!(*search_from < lits.len());
                let len = lits.len();
                for k in (*search_from..len).chain(2..*search_from) {
                    let lk = &lits[k];
                    if lit_assign!(asg, *lk) != Some(false) {
                        n -= 1;
                        let mut w = source.detach(n);
                        w.blocker = first;
                        (*watcher)[usize::from(!*lk)].register(w);
                        lits.swap(1, k);
                        // If `search_from` gets out of range, the next loop will ignore it safely;
                        // the first iteration loop becomes null.
                        *search_from = k + 1;
                        continue 'next_clause;
                    }
                }

                if first_value == Some(false) {
                    let cid = w.c;
                    asg.last_conflict = false_lit.vi();
                    asg.num_conflict += 1;
                    return cid;
                }
                let lv = lits[1..]
                    .iter()
                    .map(|l| asg.level[l.vi()])
                    .max()
                    .unwrap_or(0);
                asg.sandboxed_assign_by_implication(
                    first,
                    AssignReason::Implication(w.c, NULL_LIT),
                    lv,
                );
            }
        }
    }
    ClauseId::default()
}

impl AssignStack {
    fn sandboxed_assign_by_implication(&mut self, l: Lit, reason: AssignReason, lv: DecisionLevel) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
        debug_assert!(l.vi() < self.var.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || !cid.is_none());
        let vi = l.vi();
        self.level[vi] = lv;
        let v = &mut self.var[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(
            var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none()
        );
        set_assign!(self, l);
        self.reason[vi] = reason;
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    pub fn sandboxed_cancel_until(&mut self, lv: DecisionLevel) {
        if self.trail_lim.len() as u32 <= lv {
            return;
        }
        let lim = self.trail_lim[lv as usize];
        let mut shift = lim;
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            if self.level[vi] <= lv {
                self.trail[shift] = l;
                shift += 1;
                continue;
            }
            let v = &mut self.var[vi];
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());
            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::default();
            self.insert_heap(vi);
        }
        self.trail.truncate(shift);
        debug_assert!(self
            .trail
            .iter()
            .all(|l| var_assign!(self, l.vi()).is_some()));
        debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
        self.q_head = self.q_head.min(lim);
        if lv == self.root_level {
            self.num_restart += 1;
        }
    }
}
