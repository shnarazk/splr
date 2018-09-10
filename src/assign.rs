use types::*;
use var::Var;

#[derive(Debug)]
pub struct AssignState {
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
}

pub trait Assignment {
    fn enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> bool;
    fn uncheck_enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> ();
    fn uncheck_assume(&mut self, v: &mut Var, l: Lit) -> ();
}

impl Assignment for AssignState {
    /// This function touches:
    ///  - vars
    ///  - trail
    ///  - trail_lim
    fn uncheck_enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> () {
        v.assign = l.lbool();
        v.level = self.trail_lim.len();
        v.reason = cid;
        // mref!(self.cp, cid).locked = true;
        self.trail.push(l);
    }

    fn uncheck_assume(&mut self, v: &mut Var, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        self.uncheck_enqueue(v, l, NULL_CLAUSE);
    }
    /// This function touches:
    ///  - vars
    ///  - trail
    fn enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> bool {
        // println!("enqueue: {} by {}", l.int(), cid);
        let sig = l.lbool();
        let val = v.assign;
        if val == BOTTOM {
            v.assign = sig;
            v.level = self.trail_lim.len();
            v.reason = cid;
            // mref!(self.cp, cid).locked = true;
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }

}
