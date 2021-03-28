/// main struct AssignStack
#[cfg(any(feature = "best_phases_tracking", feature = "rephase"))]
use std::collections::HashMap;
use {
    super::{AssignIF, AssignStack, Var, VarHeapIF, VarIdHeap, VarManipulateIF, VarSelectIF},
    crate::{cdb::ClauseDBIF, solver::SolverEvent, types::*},
    std::{fmt, ops::Range, slice::Iter},
};

#[cfg(not(feature = "no_IO"))]
use std::{
    fs::File,
    io::{BufWriter, Write},
};

impl Default for AssignReason {
    fn default() -> AssignReason {
        AssignReason::None
    }
}

impl fmt::Display for AssignReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AssignReason::None => write!(f, "reason:none"),
            AssignReason::Implication(c, NULL_LIT) => write!(f, "reason:{}", c),
            AssignReason::Implication(c, _) => write!(f, "reason:biclause{}", c),
        }
    }
}

impl Default for AssignStack {
    fn default() -> AssignStack {
        AssignStack {
            assign: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            root_level: 0,
            var_order: VarIdHeap::default(),

            best_assign: false,
            build_best_at: 0,
            num_best_assign: 0,
            num_rephase: 0,

            #[cfg(feature = "best_phases_tracking")]
            best_phases: HashMap::new(),
            #[cfg(feature = "rephase")]
            phase_age: 0,

            num_vars: 0,
            num_asserted_vars: 0,
            num_eliminated_vars: 0,
            num_decision: 0,
            num_propagation: 0,
            num_conflict: 0,
            num_restart: 0,
            dpc_ema: EmaSU::new(100),
            ppc_ema: EmaSU::new(100),
            cpr_ema: EmaSU::new(100),

            ordinal: 0,
            var: Vec::new(),

            activity_decay: 0.94,
            activity_decay_default: 0.94,
            activity_anti_decay: 0.06,
            activity_ema: Ema::new(1000),
            activity_decay_step: 0.1,

            during_vivification: false,
            vivify_sandbox: (0, 0, 0),
        }
    }
}

impl<'a> IntoIterator for &'a mut AssignStack {
    type Item = &'a Lit;
    type IntoIter = Iter<'a, Lit>;
    fn into_iter(self) -> Self::IntoIter {
        self.trail.iter()
    }
}

impl From<&mut AssignStack> for Vec<i32> {
    fn from(asg: &mut AssignStack) -> Vec<i32> {
        asg.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
    }
}

impl Instantiate for AssignStack {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> AssignStack {
        let nv = cnf.num_of_variables;
        AssignStack {
            assign: vec![None; 1 + nv],
            level: vec![DecisionLevel::default(); nv + 1],
            reason: vec![AssignReason::default(); nv + 1],
            trail: Vec::with_capacity(nv),
            var_order: VarIdHeap::new(nv, nv),

            num_vars: cnf.num_of_variables,
            var: Var::new_vars(nv),

            #[cfg(feature = "EVSIDS")]
            activity_decay: config.vrw_dcy_rat * 0.6,
            #[cfg(feature = "LR_rewarding")]
            activity_decay_default: config.vrw_dcy_rat,

            activity_anti_decay: 1.0 - config.vrw_dcy_rat,
            activity_decay_step: config.vrw_dcy_stp,

            ..AssignStack::default()
        }
    }
    #[inline]
    fn handle(&mut self, e: SolverEvent) {
        match e {
            // called only by assertion on chronoBT
            // So execute everything of `assign_by_unitclause` but cancel_until(root_level)
            SolverEvent::Assert(vi) => {
                self.make_var_asserted(vi);
            }
            SolverEvent::Conflict => (),
            SolverEvent::Eliminate(vi) => {
                self.make_var_eliminated(vi);
            }
            #[allow(unused_variables)]
            SolverEvent::NewStabilizationStage(lvl) => {
                #[cfg(feature = "rephase")]
                self.select_rephasing_target(None, lvl);
            }
            SolverEvent::NewVar => {
                self.assign.push(None);
                self.level.push(DecisionLevel::default());
                self.reason.push(AssignReason::default());
                self.expand_heap();
                self.num_vars += 1;
                self.var.push(Var::from(self.num_vars));
            }
            SolverEvent::Reinitialize => {
                debug_assert_eq!(self.decision_level(), self.root_level);
                self.q_head = 0;
                self.num_eliminated_vars =
                    self.var.iter().filter(|v| v.is(Flag::ELIMINATED)).count();
                self.num_asserted_vars = if self.trail.is_empty() {
                    0
                } else {
                    self.trail.len()
                };
                self.rebuild_order();
            }
            #[cfg(feature = "clause_vivification")]
            SolverEvent::Vivify(start) => {
                if start {
                    self.during_vivification = true;
                    self.vivify_sandbox =
                        (self.num_conflict, self.num_propagation, self.num_restart);
                } else {
                    self.during_vivification = false;
                    self.num_conflict = self.vivify_sandbox.0;
                    self.num_propagation = self.vivify_sandbox.1;
                    self.num_restart = self.vivify_sandbox.2;
                }
            }
            _ => (),
        }
    }
}

impl AssignIF for AssignStack {
    fn stack(&self, i: usize) -> Lit {
        self.trail[i]
    }
    fn stack_range(&self, r: Range<usize>) -> &[Lit] {
        &self.trail[r]
    }
    fn stack_len(&self) -> usize {
        self.trail.len()
    }
    fn len_upto(&self, n: DecisionLevel) -> usize {
        self.trail_lim[n as usize]
    }
    fn stack_is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    fn stack_iter(&self) -> Iter<'_, Lit> {
        self.trail.iter()
    }
    fn decision_level(&self) -> DecisionLevel {
        self.trail_lim.len() as DecisionLevel
    }
    fn decision_vi(&self, lv: DecisionLevel) -> VarId {
        debug_assert!(0 < lv);
        self.trail[self.trail_lim[lv as usize - 1]].vi()
    }
    fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    fn assign_ref(&self) -> &[Option<bool>] {
        &self.assign
    }
    fn level_ref(&self) -> &[DecisionLevel] {
        &self.level
    }
    fn best_assigned(&mut self) -> Option<usize> {
        (self.build_best_at == self.num_propagation).then(|| self.num_vars - self.num_best_assign)
    }
    #[allow(unused_variables)]
    fn extend_model<C>(&mut self, cdb: &mut C, lits: &[Lit]) -> Vec<Option<bool>>
    where
        C: ClauseDBIF,
    {
        #[cfg(feature = "trace_elimination")]
        println!(
            "# extend_model\n - as i32: {:?}\n - as raw: {:?}",
            i32s(lits),
            lits.iter()
                .map(|l| {
                    let i = i32::from(l);
                    if i < 0 {
                        -2 * i
                    } else {
                        2 * i + 1
                    }
                })
                .collect::<Vec<_>>(),
        );
        let mut extended_model: Vec<Option<bool>> = self.assign.clone();
        if lits.is_empty() {
            return extended_model;
        }
        let mut i = lits.len() - 1;
        let mut width;
        'next: loop {
            width = usize::from(lits[i]);
            if width == 0 && i == 0 {
                break;
            }
            i -= 1;
            #[cfg(feature = "incremental_solver")]
            let mut phantom_clause = Vec::new();
            loop {
                if width <= 1 {
                    break;
                }
                let l = lits[i];
                #[cfg(feature = "incremental_solver")]
                {
                    phantom_clause.push(l);
                }
                if extended_model[l.vi()] != Some(!bool::from(l)) {
                    if i < width {
                        #[cfg(feature = "incremental_solver")]
                        {
                            for l in &lits[..i] {
                                phantom_clause.push(*l);
                            }
                            debug_assert!(1 < phantom_clause.len());
                            #[cfg(feature = "trace_elimination")]
                            println!(
                                "- pull back clause E {:?}",
                                phantom_clause.iter().map(i32::from).collect::<Vec<_>>()
                            );
                            cdb.new_clause(self, &mut phantom_clause, false, false);
                        }
                        break 'next;
                    }
                    #[cfg(feature = "incremental_solver")]
                    {
                        for l in &lits[i - width + 1..i] {
                            phantom_clause.push(*l);
                        }
                        debug_assert!(1 < phantom_clause.len());
                        #[cfg(feature = "trace_elimination")]
                        println!(
                            "- pull back clause C {:?}",
                            phantom_clause.iter().map(i32::from).collect::<Vec<_>>()
                        );
                        cdb.new_clause(self, &mut phantom_clause, false, false);
                    }
                    i -= width;
                    continue 'next;
                }
                width -= 1;
                i -= 1;
            }
            debug_assert!(width == 1);
            let l = lits[i];
            debug_assert_ne!(Some(bool::from(l)), self.assigned(l));
            #[cfg(feature = "trace_elimination")]
            println!(" - extend {}", l);
            extended_model[l.vi()] = Some(bool::from(l));
            if i < width {
                break;
            }
            i -= width;
        }
        extended_model
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == Some(true) {
                return true;
            }
        }
        false
    }
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool {
        let lits = &c.lits;
        debug_assert!(1 < lits.len());
        let l0 = lits[0];
        self.assigned(l0) == Some(true)
            && matches!(self.reason(l0.vi()), AssignReason::Implication(x, _) if x == cid)
    }
}

impl AssignStack {
    #[cfg(feature = "boundary_check")]
    pub fn dump<'a, V: IntoIterator<Item = &'a Lit, IntoIter = Iter<'a, Lit>>>(
        &mut self,
        v: V,
    ) -> Vec<(i32, DecisionLevel, bool, Option<bool>)> {
        v.into_iter()
            .map(|l| {
                (
                    i32::from(l),
                    self.level(l.vi()),
                    self.reason(l.vi()) == AssignReason::default(),
                    self.assign(l.vi()),
                )
            })
            .collect::<Vec<(i32, DecisionLevel, bool, Option<bool>)>>()
    }

    /// dump all active clauses and assertions as a CNF file.
    #[cfg(not(feature = "no_IO"))]
    #[allow(dead_code)]
    fn dump_cnf<C, V>(&mut self, cdb: &C, fname: &str)
    where
        C: ClauseDBIF,
    {
        for vi in 1..self.var.len() {
            if self.var(vi).is(Flag::ELIMINATED) {
                if self.assign.get(vi).is_some() {
                    panic!("conflicting var {} {:?}", vi, self.assign.get(vi));
                } else {
                    println!("eliminate var {}", vi);
                }
            }
        }
        if let Ok(out) = File::create(&fname) {
            let mut buf = BufWriter::new(out);
            let nv = self.num_vars;
            let nc: usize = cdb.len() - 1;
            buf.write_all(format!("p cnf {} {}\n", self.num_vars, nc + nv).as_bytes())
                .unwrap();
            for c in cdb.iter().skip(1) {
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

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
        let levels = self.decision_level();
        let c = |i| match i {
            0 => {
                let a = self.len_upto(i);
                (0, &v[0..a])
            }
            x if x == levels => {
                let a = self.len_upto(levels - 1);
                (levels, &v[a..])
            }
            x => {
                let a = self.len_upto(x - 1);
                (x, &v[a..self.len_upto(x)])
            }
        };
        if 0 < levels {
            write!(
                f,
                "ASG:: trail({}):{:?}\n      stats: level: {}, asserted: {}, eliminated: {}",
                self.trail.len(),
                (0..=levels).map(c).collect::<Vec<_>>(),
                levels,
                self.num_asserted_vars,
                self.num_eliminated_vars,
            )
        } else {
            write!(
                f,
                "ASG:: trail({}):[(0, {:?})]\n      level: {}, asserted: {}, eliminated: {}",
                self.trail.len(),
                &v,
                levels,
                self.num_asserted_vars,
                self.num_eliminated_vars,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::PropagateIF;

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }
    #[test]
    fn test_propagation() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        // [] + 1 => [1]
        assert!(asg.assign_at_root_level(lit(1)).is_ok());
        assert_eq!(asg.trail, vec![lit(1)]);

        // [1] + 1 => [1]
        assert!(asg.assign_at_root_level(lit(1)).is_ok());
        assert_eq!(asg.trail, vec![lit(1)]);

        // [1] + 2 => [1, 2]
        assert!(asg.assign_at_root_level(lit(2)).is_ok());
        assert_eq!(asg.trail, vec![lit(1), lit(2)]);

        // [1, 2] + -1 => ABORT & [1, 2]
        assert!(asg.assign_at_root_level(lit(-1)).is_err());
        assert_eq!(asg.decision_level(), 0);
        assert_eq!(asg.stack_len(), 2);

        // [1, 2] + 3 => [1, 2, 3]
        asg.assign_by_decision(lit(3));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3)]);
        assert_eq!(asg.decision_level(), 1);
        assert_eq!(asg.stack_len(), 3);
        assert_eq!(asg.len_upto(0), 2);

        // [1, 2, 3] + 4 => [1, 2, 3, 4]
        asg.assign_by_decision(lit(4));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        assert_eq!(asg.decision_level(), 2);
        assert_eq!(asg.stack_len(), 4);
        assert_eq!(asg.len_upto(1), 3);

        // [1, 2, 3] => [1, 2]
        asg.cancel_until(1);
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3)]);
        assert_eq!(asg.decision_level(), 1);
        assert_eq!(asg.stack_len(), 3);
        assert_eq!(asg.trail_lim, vec![2]);
        assert_eq!(asg.assigned(lit(1)), Some(true));
        assert_eq!(asg.assigned(lit(-1)), Some(false));
        assert_eq!(asg.assigned(lit(4)), None);

        // [1, 2, 3] => [1, 2, 3, 4]
        asg.assign_by_decision(lit(4));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        assert_eq!(asg.level[lit(4).vi()], 2);
        assert_eq!(asg.trail_lim, vec![2, 3]);

        // [1, 2, 3, 4] => [1, 2, -4]
        asg.assign_by_unitclause(Lit::from(-4i32));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(-4)]);
        assert_eq!(asg.decision_level(), 0);
        assert_eq!(asg.stack_len(), 3);

        assert_eq!(asg.assigned(lit(-4)), Some(true));
        assert_eq!(asg.assigned(lit(-3)), None);
    }
}
