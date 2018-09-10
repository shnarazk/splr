#![allow(unreachable_code)]
use clause::Clause;
use clause::ClausePack;
use types::*;
use clause::ClauseIndex;
use var::Var;

pub const DEBUG: usize = 27728;
pub const WATCHING: VarId = 2685;

pub trait ClausePropagation {
    fn check_garbage(&mut self) -> ();
    fn garbage_collect(&mut self, vars: &Vec<Var>) -> ();
    fn count(&self, target: Lit) -> usize;
    fn detach_to_trash(&mut self, c: &mut Clause, index: usize) -> ClauseIndex;
    fn seek_from(&self, ci: ClauseIndex, p: Lit) -> bool;
    fn print_watcher(&self, p: Lit) -> ();
    fn check_clause(&self, mes: &str, ci: ClauseIndex);
    fn check_lit(&self, vars: &Vec<Var>, mes: &str, lit: Lit) -> ();
}

impl ClausePropagation for ClausePack {
    fn check_garbage(&mut self) -> () {
        {
            for c in &self.clauses[1..] {
                if c.dead {
                    panic!("fail to gather all garbages. An exception {:#} {}, {}",
                           c,
                           self.seek_from(c.index, c.lit[0]),
                           self.seek_from(c.index, c.lit[1]),
                           );
                     continue;
                }
            }
        }
    }
    fn garbage_collect(&mut self, vars: &Vec<Var>) -> () {
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
            for l in 2..vars.len()*2 {
                let vi = (l as Lit).vi();
                let mut pri = &mut self.watcher[l] as *mut ClauseId;
                let mut ci = self.watcher[l];
                'next_clause: while ci != NULL_CLAUSE {
                    let c = &mut self.clauses[ci] as *mut Clause;
                    if vi == WATCHING || (*c).index == DEBUG {
                        println!("# garbage collect: traverser finds on {} : {:#}", vi, *c);
                    }
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
                        *pri = self.detach_to_trash(&mut *c, 0);
                        ci = *pri;
                    } else if (*c).lit[1].negate() == l as Lit {
                        *pri = self.detach_to_trash(&mut *c, 1);
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
                if (*c).index == DEBUG {
                    // println!("garbage traverser finds: {:#} on GARBGE link", *c);
                }
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
    fn count(&self, target: Lit) -> usize {
        let mut ci = self.watcher[target.negate() as usize];
        let mut cnt = 0;
        while ci != NULL_CLAUSE {
            cnt += 1;
            let c = &self.clauses[ci];
            if ci == c.next_watcher[(c.lit[0] != target) as usize] {
                panic!("{} is looping!", target);
            }
            if cnt % 10000 == 0 && false {
                //let cc = &self.clauses[self.watcher[target.negate() as usize]];
                // println!("#{} = {}, {:#}", target, cnt, cc);
                // cc = &self.clauses[cc.next_watcher[(cc.lit[0] != target) as usize]];
                // println!("#{} = {}, {:#}", target, cnt, cc);
            }
            ci = c.next_watcher[(c.lit[0] != target) as usize];
        }
        cnt
    }
    fn detach_to_trash(&mut self, c: &mut Clause, index: usize) -> ClauseIndex {
        let other = (index ^ 1) as usize;
        // if c.index == DEBUG {
        //     println!("detach_to_trash before: {:#} to {} {} at {}", c, index, c.lit[other], other);
        // }
        debug_assert!(c.dead);
        debug_assert_ne!(c.lit[index], GARBAGE_LIT);
        debug_assert_ne!(c.lit[index], RECYCLE_LIT);
        // print!("{}detach_to_trash: ", self.to_kind());
        // self.print_watcher(GARBAGE_LIT.negate());
        // print!("{}detach_to_trash: ", self.to_kind());
        // self.print_watcher(RECYCLE_LIT.negate());
        // if c.index == DEBUG {
        //     println!("{}detach_to_trash after: {:#} {} {}", self.to_kind(), c, GARBAGE_LIT, c.lit[index]);
        // }
        let pre = self.count(GARBAGE_LIT);
        let ryc = self.count(RECYCLE_LIT);
        c.lit[index] = GARBAGE_LIT;
        unsafe {
            let garbage = &mut self.watcher[(GARBAGE_LIT.negate()) as usize] as *mut ClauseId;
            let next = c.next_watcher[index];
            if c.lit[other] == RECYCLE_LIT {
                panic!("AAAA");
            }
            if c.lit[other] == GARBAGE_LIT {
                // println!(" - double released");
                if !self.seek_from(c.index, GARBAGE_LIT) {
                    panic!(" - A garbage didn't entered in trash {:#}", c);
                }
                c.next_watcher[index] = c.next_watcher[other];
                // println!(" - detach completely {:#}", c);
            } else {
                c.next_watcher[index] = *garbage;
                *garbage = c.index;
            }
            if c.lit[other] != GARBAGE_LIT && pre + ryc + 1 != self.count(GARBAGE_LIT) + self.count(RECYCLE_LIT) {
                self.print_watcher(GARBAGE_LIT);
                panic!(" - detach_to_trash: inconsistency found gar {} => {}, ryc {} => {}, {:#}", pre, self.count(GARBAGE_LIT), ryc, self.count(RECYCLE_LIT), c);
            } else {
                // println!(" - success to detach {:#} #{} + #{} => #{} + #{}", c, pre, ryc, self.count(GARBAGE_LIT), self.count(RECYCLE_LIT));
                // print!(" - ");
                // self.print_watcher(GARBAGE_LIT.negate());
                // print!(" - ");
                // self.print_watcher(RECYCLE_LIT.negate());
            }
            next
        }
    }
    // returns false when error.
    fn seek_from(&self, ci: ClauseIndex, p: Lit) -> bool {
        let mut i = self.watcher[p.negate() as usize];
        while i != NULL_CLAUSE {
            let c = &self.clauses[i];
            if c.index == ci {
                return true;
            }
            let index = if c.lit[0] == p { 0 } else { 1 };
            i = c.next_watcher[index];
        }
        false
    }
    fn print_watcher(&self, p: Lit) -> () {
        match p {
            GARBAGE_LIT => print!("watcher[garbage] = "),
            RECYCLE_LIT => print!("watcher[recycle] = "),
            x => print!("watcher[{}] = ", x.int()),
        };
        let mut i = self.watcher[p as usize];
        while i != NULL_CLAUSE {
            let c = &self.clauses[i];
            print!("{}, ", i);
            let index = match () {
                _ if c.lit[0].negate() == p => 0,
                _ if c.lit[1].negate() == p => 1,
                _ => panic!("the literal {} is not a watcher for {:#}", p, c),
            };
            i = c.next_watcher[index];
        }
        println!("0");
    }
    fn check_clause(&self, mes: &str, ci: ClauseIndex) {
        if ci != DEBUG {
            return;
        }
        let c = &self.clauses[DEBUG];
        let l0 = c.lit[0];
        let l1 = c.lit[1];
        let r0 = self.seek_from(c.index, l0);
        let r1 = self.seek_from(c.index, l1);
        if r0 || r1 {
            println!("No problem on watchers of {} clause {} '{}'; watching {} and {}",
                     if c.dead { "dead" } else { "" },
                     c.index, mes, l0.show(), l1.show());
        } else {
            println!("Assersion failed by {} at '{}', lit0({}): {}, lit1({}): {}",
                     c.index,
                     mes,
                     l0.show(),
                     r0,
                     l1.show(),
                     r1,
            );
            self.print_watcher(l0.negate());
            self.print_watcher(l1.negate());
            println!("{:#}", c);
            panic!("panic");
        }
    }
    fn check_lit(&self, vars: &Vec<Var>, mes: &str, lit: Lit) -> () {
        let vi = lit.vi();
        if vi == WATCHING {
            let p = vi.lit(LTRUE);
            let n = vi.lit(LFALSE);
            let found_in_p = self.seek_from(DEBUG, p);
            let found_in_n = self.seek_from(DEBUG, n);
            if (p.lbool() == vars[vi].phase || p.lbool() == vars[vi].assign) && !found_in_p && !found_in_n {
                return;
            }
            if found_in_p || found_in_n {
                println!("Watcher state: {} on {}", mes, lit.int());
                if found_in_p { print!(" - "); self.print_watcher(n); }
                if found_in_n { print!(" - "); self.print_watcher(p); }
            }
            println!("Check lit: {} on {} not including C{}", mes, lit.int(), DEBUG);
        }
    }
}
