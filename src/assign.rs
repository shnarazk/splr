use types::*;
use var::Var;

pub trait Assignment {
    fn decision_level(&self) -> usize;
    fn enqueue(&mut self, assign: &mut [Lbool], v: &mut Var, l: Lit, cid: ClauseId) -> bool;
    fn uncheck_enqueue(&mut self, assign: &mut [Lbool], v: &mut Var, l: Lit, cid: ClauseId) -> ();
    fn uncheck_assume(&mut self, assign: &mut [Lbool], v: &mut Var, l: Lit) -> ();
}

#[derive(Debug)]
pub struct AssignState {
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
}

impl Assignment for AssignState {
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    /// WARNING: you have to lock the clause by yourself.
    fn enqueue(&mut self, assign: &mut [Lbool], v: &mut Var, l: Lit, cid: ClauseId) -> bool {
        // println!("enqueue: {} by {}", l.int(), cid);
        let sig = l.lbool();
        let val = assign[l.vi()];
        assign[l.vi()] = sig;
        if val == BOTTOM {
            v.level = self.trail_lim.len();
            v.reason = cid;
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
    fn uncheck_enqueue(&mut self, assign: &mut [Lbool], v: &mut Var, l: Lit, cid: ClauseId) -> () {
        assign[l.vi()] = l.lbool();
        v.level = self.trail_lim.len();
        v.reason = cid;
        // mref!(self.cp, cid).locked = true;
        self.trail.push(l);
    }
    fn uncheck_assume(&mut self, assign: &mut [Lbool], v: &mut Var, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        self.uncheck_enqueue(assign, v, l, NULL_CLAUSE);
    }
}
