#![allow(unreachable_code)]
use clause::Clause;
use clause::ClausePack;
use types::*;
use clause::ClauseIndex;

// for ClausePack
pub trait ClauseReduction {
    fn garbage_collect(&mut self) -> ();
    fn detach(&mut self, c: &mut Clause, index: usize) -> ClauseIndex;
}

impl ClauseReduction for ClausePack {
    fn garbage_collect(&mut self) -> () {
        if self.watcher[GARBAGE_LIT.negate() as usize] == NULL_CLAUSE {
            return;
        }
        let mut ci = self.watcher[GARBAGE_LIT.negate() as usize];
        while ci != NULL_CLAUSE {
            let c = &self.clauses[ci];
            debug_assert!(c.dead);
            debug_assert!(c.lit[0] == GARBAGE_LIT || c.lit[1] == GARBAGE_LIT);
            let index = (c.lit[0] != GARBAGE_LIT) as usize;
            ci = c.next_watcher[index];
        }
        unsafe {
            for l in 2..self.watcher.len() {
                let vi = (l as Lit).vi();
                let mut pri = &mut self.watcher[l] as *mut ClauseId;
                let mut ci = self.watcher[l];
                'next_clause: while ci != NULL_CLAUSE {
                    let c = &mut self.clauses[ci] as *mut Clause;
                    // if vi == WATCHING || (*c).index == DEBUG { println!("# garbage collect: traverser finds on {} : {:#}", vi, *c); }
                    if !(*c).dead {
                        debug_assert!(!(*c).dead);
                        if (*c).lit[0].vi() == vi {
                            pri = &mut (*c).next_watcher[0];
                            ci = *pri;
                        } else {
                            pri = &mut (*c).next_watcher[1];
                            ci = *pri;
                        }
                        continue;
                    }
                    debug_assert!((*c).dead);
                    if (*c).lit[0] == GARBAGE_LIT && (*c).lit[1] == GARBAGE_LIT {
                        panic!("not be");
                    } else if (*c).lit[0].negate() == l as Lit {
                        *pri = self.detach(&mut *c, 0);
                        ci = *pri;
                    } else if (*c).lit[1].negate() == l as Lit {
                        *pri = self.detach(&mut *c, 1);
                        ci = *pri;
                    } else {
                        panic!("xxxxx {:?}", (*c).lit);
                    }
                }
            }
            // recycle garbages
            let recycled = &mut self.watcher[RECYCLE_LIT.negate() as usize] as *mut ClauseId;
            let mut pri = &mut self.watcher[GARBAGE_LIT.negate() as usize] as *mut ClauseId;
            let mut ci = self.watcher[GARBAGE_LIT.negate() as usize];
            while ci != NULL_CLAUSE {
                let c = &mut self.clauses[ci] as *mut Clause;
                if !(*c).dead {
                    // self.print_watcher(0);
                    // self.print_watcher(1);
                    panic!("not dead {:#}", *c);
                }
                debug_assert!((*c).dead);
                // if (*c).index == DEBUG { println!("garbage traverser finds: {:#} on GARBGE link", *c); }
                if (*c).lit[0] == GARBAGE_LIT && (*c).lit[1] == GARBAGE_LIT {
                    // println!("move {} to recycler", (*c).index);
                    // if (*c).index == DEBUG { println!("here comes!"); }
                    let next = (*c).next_watcher[0];
                    *pri = (*c).next_watcher[0];
                    (*c).lit[0] = RECYCLE_LIT;
                    (*c).lit[1] = RECYCLE_LIT;
                    (*c).next_watcher[0] = *recycled;
                    (*c).next_watcher[1] = *recycled;
                    *recycled = ci; // (*c).next_watcher[0];
                    (*c).dead = false;
                    ci = next;
                    // print!("recycler: ");
                    // self.print_watcher(GARBAGE_LIT.negate());
                } else if (*c).lit[0] != GARBAGE_LIT && (*c).lit[1] != GARBAGE_LIT {
                    println!("very strange {}", *c);
                } else {
                    let index = ((*c).lit[0] != GARBAGE_LIT) as usize; // the other might have still active path
                    // if (*c).index == DEBUG || true { println!("half processed! {:#}", *c); }
                    ci = (*c).next_watcher[index];
                    pri = &mut (*c).next_watcher[index];
                }
            }
        }
        debug_assert_eq!(self.watcher[0], NULL_CLAUSE);
    }
    fn detach(&mut self, c: &mut Clause, index: usize) -> ClauseIndex {
        let other = (index ^ 1) as usize;
        // if c.index == DEBUG { println!("detach before: {:#} to {} {} at {}", c, index, c.lit[other], other); }
        debug_assert!(c.dead);
        debug_assert_ne!(c.lit[index], GARBAGE_LIT);
        debug_assert_ne!(c.lit[index], RECYCLE_LIT);
        // print!("{}detach: ", self.to_kind());
        // self.print_watcher(GARBAGE_LIT.negate());
        // print!("{}detach: ", self.to_kind());
        // self.print_watcher(RECYCLE_LIT.negate());
        // if c.index == DEBUG {
        //     println!("{}detach after: {:#} {} {}", self.to_kind(), c, GARBAGE_LIT, c.lit[index]);
        // }
        // let pre = self.count(GARBAGE_LIT);
        // let ryc = self.count(RECYCLE_LIT);
        c.lit[index] = GARBAGE_LIT;
        let garbage = &mut self.watcher[(GARBAGE_LIT.negate()) as usize];
        let next = c.next_watcher[index];
        // if c.lit[other] == RECYCLE_LIT { panic!("AAAA"); }
        if c.lit[other] == GARBAGE_LIT {
            // println!(" - double released");
            // if !self.seek_from(c.index, GARBAGE_LIT) { panic!(" - A garbage didn't entered in trash {:#}", c); }
            c.next_watcher[index] = c.next_watcher[other];
            // println!(" - detach completely {:#}", c);
        } else {
            c.next_watcher[index] = *garbage;
            *garbage = c.index;
        }
        // if c.lit[other] != GARBAGE_LIT && pre + ryc + 1 != self.count(GARBAGE_LIT) + self.count(RECYCLE_LIT) {
        //     self.print_watcher(GARBAGE_LIT);
        //     panic!(" - detach: inconsistency found gar {} => {}, ryc {} => {}, {:#}", pre, self.count(GARBAGE_LIT), ryc, self.count(RECYCLE_LIT), c);
        // } else {
        //     // println!(" - success to detach {:#} #{} + #{} => #{} + #{}", c, pre, ryc, self.count(GARBAGE_LIT), self.count(RECYCLE_LIT));
        //     // print!(" - ");
        //     // self.print_watcher(GARBAGE_LIT.negate());
        //     // print!(" - ");
        //     // self.print_watcher(RECYCLE_LIT.negate());
        // }
        next
    }
}
