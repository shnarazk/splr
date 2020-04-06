/// Crate 'solver' provides the top-level API as a SAT solver.
use {
    crate::{
        assign::{AssignIF, AssignStack, VarSelectionIF},
        clause::{ClauseDB, ClauseDBIF},
        eliminate::{EliminateIF, Eliminator},
        restart::{RestartIF, Restarter, RestarterModule},
        state::{PhaseMode, Stat, State, StateIF},
        types::*,
        var::{VarDB, VarDBIF, VarRewardIF},
    },
    std::{
        convert::TryFrom,
        fs::File,
        io::{BufRead, BufReader},
        slice::Iter,
    },
};

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverIF {
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// IO error by failing to load a CNF file.
    fn build(config: &Config) -> Result<Solver, SolverError>;
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
    /// add a vector of `Lit` as a clause to the solver.
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

/// Normal results returned by Solver.
#[derive(Debug, PartialEq)]
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT,
}

/// The return type of `Solver::solve`.
/// This captures the following three cases:
/// * `Certificate::SAT` -- solved with a satisfiable assignment set,
/// * `Certificate::UNSAT` -- proved that it's an unsatisfiable problem, and
/// * `SolverException::*` -- caused by a bug
pub type SolverResult = Result<Certificate, SolverError>;

/// The SAT solver object consisting of 6 sub modules.
/// ```
/// use std::convert::TryFrom;
/// use crate::splr::{state::{State, StateIF}, types::*};
/// use crate::splr::solver::{SatSolverIF, Solver, Certificate::*};
///
/// let mut s = Solver::try_from("tests/sample.cnf").expect("can't load");
/// assert_eq!(s.state.num_vars, 250);
/// assert_eq!(s.state.num_unsolved_vars(), 250);
/// if let Ok(SAT(v)) = s.solve() {
///     assert_eq!(v.len(), 250);
///     // But don't expect `s.state.num_unsolved_vars() == 0` at this point.
///     // It returns the nubmer of vars which were assigned at decision level 0.
/// } else {
///     panic!("It should be satisfied!");
/// }
/// assert_eq!(Solver::try_from("tests/unsat.cnf").expect("can't load").solve(), Ok(UNSAT));
/// ```
#[derive(Debug)]
pub struct Solver {
    /// assignment management
    pub asgs: AssignStack,
    /// clause container
    pub cdb: ClauseDB,
    /// clause and variable elimination
    pub elim: Eliminator,
    /// restart management
    pub rst: Restarter,
    /// misc data holder
    pub state: State,
    /// var container
    pub vdb: VarDB,
}

impl Default for Solver {
    fn default() -> Solver {
        Solver {
            asgs: AssignStack::default(),
            cdb: ClauseDB::default(),
            elim: Eliminator::default(),
            rst: Restarter::instantiate(&Config::default(), &CNFDescription::default()),
            state: State::default(),
            vdb: VarDB::default(),
        }
    }
}

impl Instantiate for Solver {
    /// ```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use splr::solver::Solver;
    /// let s = Solver::instantiate(&Config::default(), &CNFDescription::default());
    ///```
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Solver {
        Solver {
            asgs: AssignStack::instantiate(config, cnf),
            cdb: ClauseDB::instantiate(config, cnf),
            elim: Eliminator::instantiate(config, cnf),
            rst: Restarter::instantiate(config, &cnf),
            state: State::instantiate(config, cnf),
            vdb: VarDB::instantiate(config, cnf),
        }
    }
}

impl TryFrom<&str> for Solver {
    type Error = SolverError;
    /// return a new solver bulid for a CNF file.
    ///
    /// # Example
    /// ```
    /// use std::convert::TryFrom;
    /// use crate::splr::solver::{SatSolverIF, Solver};
    ///
    /// let mut s = Solver::try_from("tests/sample.cnf").expect("fail to load");
    ///```
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let config = Config::from(s);
        Solver::build(&config)
    }
}

macro_rules! final_report {
    ($asgs: expr, $cdb: expr, $elim: expr, $rst: expr, $state: expr, $vdb: expr) => {
        let c = $state.config.no_color;
        let q = $state.config.quiet_mode;
        $state.config.no_color = true;
        $state.config.quiet_mode = false;
        if q {
            $state.progress_header();
        }
        $state.progress($asgs, $cdb, $elim, $rst, $vdb, None);
        $state.config.no_color = c;
        $state.config.quiet_mode = q;
    };
}

impl SatSolverIF for Solver {
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{Certificate, SatSolverIF, Solver};
    ///
    /// let config = Config::from("tests/sample.cnf");
    /// if let Ok(mut s) = Solver::build(&config) {
    ///     let res = s.solve();
    ///     assert!(res.is_ok());
    ///     assert_ne!(res.unwrap(), Certificate::UNSAT);
    /// }
    ///```
    fn solve(&mut self) -> SolverResult {
        let Solver {
            ref mut asgs,
            ref mut cdb,
            ref mut elim,
            ref mut rst,
            ref mut state,
            ref mut vdb,
        } = self;
        if cdb.check_size().is_err() {
            return Err(SolverError::OutOfMemory);
        }
        // NOTE: splr doesn't deal with assumptions.
        // s.root_level = 0;
        state.num_solved_vars = asgs.len();
        state.progress_header();
        state.progress(asgs, cdb, elim, rst, vdb, Some("initialization phase"));
        state.flush("loading...");
        const USE_PRE_PROCESSING_ELIMINATOR: bool = true;

        //
        //## Propagate all trivial literals (an essential step)
        //
        // Set appropriate phases and push all the unit clauses to assign stack.
        // To do so, we use eliminator's ocuur list.
        // Thus we have to call `activate` and `prepare` firstly, to build occur lists.
        // Otherwise all literals are assigned wrongly.
        state.flush("phasing...");
        elim.activate();
        elim.prepare(cdb, vdb, true);
        for vi in 1..vdb.len() {
            let v = &mut vdb[vi];
            if v.assign.is_some() {
                continue;
            }
            match elim.stats(vi) {
                (_, 0) => {
                    let l = Lit::from_assign(vi, true);
                    if asgs.assign_at_rootlevel(vdb, l).is_err() {
                        return Ok(Certificate::UNSAT);
                    }
                }
                (0, _) => {
                    let l = Lit::from_assign(vi, false);
                    if asgs.assign_at_rootlevel(vdb, l).is_err() {
                        return Ok(Certificate::UNSAT);
                    }
                }
                (p, m) => {
                    v.set(Flag::PHASE, m < p);
                    elim.enqueue_var(vdb, vi, false);
                }
            }
        }
        //
        //## Run eliminator
        //
        if !USE_PRE_PROCESSING_ELIMINATOR || !elim.enable {
            elim.stop(cdb, vdb);
        }
        if USE_PRE_PROCESSING_ELIMINATOR && elim.enable {
            state.flush("simplifying...");
            // if 20_000_000 < state.target.num_of_clauses {
            //     state.elim_eliminate_grow_limit = 0;
            //     state.elim_eliminate_loop_limit = 1_000_000;
            //     state.elim_subsume_loop_limit = 2_000_000;
            // }
            if elim.simplify(asgs, cdb, state, vdb).is_err() {
                // Why inconsistent? Because the CNF contains a conflict, not an error!
                // Or out of memory.
                final_report!(asgs, cdb, elim, rst, state, vdb);
                if cdb.check_size().is_err() {
                    return Err(SolverError::OutOfMemory);
                }
                return Ok(Certificate::UNSAT);
            }
            for v in &mut vdb[1..] {
                if v.assign.is_some() || v.is(Flag::ELIMINATED) {
                    continue;
                }
                match elim.stats(v.index) {
                    (_, 0) => (),
                    (0, _) => (),
                    (p, m) if m * 10 < p => v.turn_on(Flag::PHASE),
                    (p, m) if p * 10 < m => v.turn_off(Flag::PHASE),
                    _ => (),
                }
            }
            vdb.initialize_reward(elim.sorted_iterator());
        }
        asgs.rebuild_order(vdb);
        state.progress(asgs, cdb, elim, rst, vdb, None);

        //
        //## Search
        //
        let answer = search(asgs, cdb, elim, rst, state, vdb);
        final_report!(asgs, cdb, elim, rst, state, vdb);
        match answer {
            Ok(true) => {
                elim.extend_model(vdb);
                #[cfg(debug)]
                {
                    if let Some(cid) = cdb.validate(vdb, true) {
                        panic!(
                            "Level {} generated assignment({:?}) falsifies {}:{:?}",
                            asgs.level(),
                            cdb.validate(vdb, false).is_none(),
                            cid,
                            vdb.dump(asgs, &cdb[cid]),
                        );
                    }
                }
                if cdb.validate(vdb, true).is_some() {
                    return Err(SolverError::SolverBug);
                }
                let vals = vdb[1..]
                    .iter()
                    .map(|v| i32::from(Lit::from(v)))
                    .collect::<Vec<i32>>();
                asgs.cancel_until(vdb, 0);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::NullLearnt) => {
                asgs.cancel_until(vdb, 0);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                asgs.cancel_until(vdb, 0);
                Err(e)
            }
        }
    }
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{SatSolverIF, Solver};
    ///
    /// let config = Config::from("tests/sample.cnf");
    /// assert!(Solver::build(&config).is_ok());
    ///```
    fn build(config: &Config) -> Result<Solver, SolverError> {
        let CNFReader { cnf, reader } = CNFReader::try_from(&config.cnf_file)?;
        Solver::instantiate(config, &cnf).inject(reader)
    }
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, lits: &mut Vec<Lit>) -> Option<ClauseId> {
        let Solver {
            ref mut asgs,
            ref mut cdb,
            ref mut elim,
            ref mut vdb,
            ..
        } = self;
        if lits.is_empty() {
            return None;
        }
        debug_assert!(asgs.level() == 0);
        if lits.iter().any(|l| vdb.assigned(*l).is_some()) {
            cdb.certificate_add(lits);
        }
        lits.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means tautology.
        for i in 0..lits.len() {
            let li = lits[i];
            let sat = vdb.assigned(li);
            if sat == Some(true) || !li == l_ {
                return Some(ClauseId::default());
            } else if sat != Some(false) && li != l_ {
                lits[j] = li;
                j += 1;
                l_ = li;
            }
        }
        lits.truncate(j);
        match lits.len() {
            0 => None, // Empty clause is UNSAT.
            1 => asgs
                .assign_at_rootlevel(vdb, lits[0])
                .map_or(None, |_| Some(ClauseId::default())),
            _ => {
                let cid = cdb.new_clause(asgs, lits, None::<&mut VarDB>);
                elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
                Some(cid)
            }
        }
    }
}

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
#[inline]
fn search(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    vdb: &mut VarDB,
) -> Result<bool, SolverError> {
    let mut a_decision_was_made = false;
    rst.update(RestarterModule::Luby, 0);
    loop {
        vdb.reward_update();
        let ci = asgs.propagate(cdb, vdb);
        if ci == ClauseId::default() {
            if state.num_vars <= asgs.len() + state.num_eliminated_vars {
                return Ok(true);
            }

            //
            //## DYNAMIC FORCING RESTART based on LBD values, updated by conflict
            //
            state.last_asg = asgs.len();
            if rst.force_restart() {
                asgs.cancel_until(vdb, state.root_level);
            }
        } else {
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NoDecisionConflict] += 1;
            }
            if asgs.level() == state.root_level {
                analyze_final(asgs, state, vdb, &cdb[ci]);
                return Ok(false);
            }
            // The above condition isn't enough if you use chronoBT
            // due to the incoherence between the current level and conflicting level.
            // So we need to add a catch here.
            let level = asgs.level_ref();
            if cdb[ci].iter().all(|l| level[l.vi()] == 0) {
                return Ok(false);
            }
            handle_conflict(asgs, cdb, elim, rst, state, vdb, ci)?;
        }
        // Simplification has been postponed because chronoBT was used.
        if asgs.level() == state.root_level {
            // `elim.to_eliminate` is increased much in particular when vars are solved or
            // learnts are small. We don't need to count the number of solved vars.
            if state.config.elim_trigger < state.to_eliminate as usize {
                state.to_eliminate = 0.0;
                if elim.enable {
                    elim.activate();
                }
                elim.simplify(asgs, cdb, state, vdb)?;
            }
            // By simplification, we may get further solutions.
            if state.num_solved_vars < asgs.len() {
                rst.update(RestarterModule::Reset, 0);
                state.num_solved_vars = asgs.len();
            }
        }
        if !asgs.remains() {
            let vi = asgs.select_var(vdb);
            let p = match state.phase_select {
                PhaseMode::BestRnd => {
                    let num_propagation = asgs.exports().1;
                    match num_propagation % 8 {
                        0 => num_propagation % 16 == 1,
                        4 => vdb[vi].is(Flag::PHASE),
                        _ => vdb[vi].is(Flag::BEST_PHASE),
                    }
                }
                PhaseMode::Invert => !vdb[vi].is(Flag::PHASE),
                PhaseMode::Latest => vdb[vi].is(Flag::PHASE),
            };
            asgs.assign_by_decision(vdb, Lit::from_assign(vi, p));
            state[Stat::Decision] += 1;
            a_decision_was_made = true;
        }
    }
}

#[allow(clippy::cognitive_complexity)]
#[inline]
fn handle_conflict(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    vdb: &mut VarDB,
    ci: ClauseId,
) -> MaybeInconsistent {
    let (ncnfl, _num_propagation, asgs_num_restart) = asgs.exports();
    // If we can settle this conflict w/o restart, solver will get a big progress.
    let switch_chronobt = if ncnfl < 1000 || asgs.recurrent_conflicts() {
        Some(false)
    } else {
        None
    };
    rst.update(RestarterModule::Counter, ncnfl);

    if 0 < state.last_asg {
        rst.update(RestarterModule::ASG, asgs.len());
        state.last_asg = 0;
    }

    //
    //## DYNAMIC BLOCKING RESTART based on ASG, updated on conflict path
    //
    rst.block_restart();
    let cl = asgs.level();
    let mut use_chronobt = switch_chronobt.unwrap_or(0 < state.config.cbt_thr);
    if use_chronobt {
        let level = asgs.level_ref();
        let c = &cdb[ci];
        let lcnt = c.iter().filter(|l| level[l.vi()] == cl).count();
        if 1 == lcnt {
            debug_assert!(c.iter().any(|l| level[l.vi()] == cl));
            let decision = *c.iter().find(|l| level[l.vi()] == cl).unwrap();
            let snd_l = c
                .iter()
                .map(|l| level[l.vi()])
                .filter(|l| *l != cl)
                .max()
                .unwrap_or(0);
            if 0 < snd_l {
                // If the conflicting clause contains one literallfrom the maximal
                // decision level, we let BCP propagating that literal at the second
                // highest decision level in conflicting cls.
                // PREMISE: 0 < snd_l
                asgs.cancel_until(vdb, snd_l - 1);
                debug_assert!(
                    asgs.iter().all(|l| l.vi() != decision.vi()),
                    format!("lcnt == 1: level {}, snd level {}", cl, snd_l)
                );
                asgs.assign_by_decision(vdb, decision);
                return Ok(());
            }
        }
    }
    // conflicting level
    // By mixing two restart modes, we must assume a conflicting level is under the current decision level,
    // even if `use_chronobt` is off, because `use_chronobt` is a flag for future behavior.
    let cl = {
        let cl = asgs.level();
        let c = &cdb[ci];
        let level = asgs.level_ref();
        let lv = c.iter().map(|l| level[l.vi()]).max().unwrap_or(0);
        if lv < cl {
            asgs.cancel_until(vdb, lv);
            lv
        } else {
            cl
        }
    };
    debug_assert!(
        cdb[ci].iter().any(|l| asgs.level_ref()[l.vi()] == cl),
        format!(
            "use_{}: {:?}, {:?}",
            use_chronobt,
            cl,
            cdb[ci]
                .iter()
                .map(|l| (i32::from(*l), asgs.level_ref()[l.vi()]))
                .collect::<Vec<_>>(),
        )
    );
    // backtrack level by analyze
    let bl_a = conflict_analyze(asgs, cdb, state, vdb, ci).max(state.root_level);
    if state.new_learnt.is_empty() {
        #[cfg(debug)]
        {
            println!(
                "empty learnt at {}({}) by {:?}",
                cl,
                vdb[asgs.decision_vi(cl)].reason == ClauseId::default(),
                vdb.dump(asgs, &cdb[ci]),
            );
        }
        return Err(SolverError::NullLearnt);
    }
    // vdb.bump_vars(asgs, cdb, ci);
    let new_learnt = &mut state.new_learnt;
    let l0 = new_learnt[0];
    // assert: 0 < cl, which was checked already by new_learnt.is_empty().

    // NCB places firstUIP on level bl, while CB does it on level cl.
    // Therefore the condition to use CB is: activity(firstUIP) < activity(v(bl)).
    // PREMISE: 0 < bl, because asgs.decision_vi accepts only non-zero values.
    use_chronobt &= switch_chronobt.unwrap_or(
        bl_a == 0
            || state.config.cbt_thr + bl_a <= cl
            || vdb.activity(l0.vi()) < vdb.activity(asgs.decision_vi(bl_a)),
    );

    // (assign level, backtrack level)
    let (al, bl) = if use_chronobt {
        (
            {
                let level = asgs.level_ref();
                new_learnt[1..]
                    .iter()
                    .map(|l| level[l.vi()])
                    .max()
                    .unwrap_or(0)
            },
            cl - 1,
        )
    } else {
        (bl_a, bl_a)
    };
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        //
        //## PARTIAL FIXED SOLUTION by UNIT LEARNT CLAUSE GENERATION
        //
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        if use_chronobt {
            asgs.cancel_until(vdb, bl);
            debug_assert!(asgs.iter().all(|l| l.vi() != l0.vi()));
            asgs.assign_by_implication(vdb, l0, AssignReason::default(), 0);
        } else {
            asgs.assign_by_unitclause(vdb, l0);
        }
        state.last_solved = ncnfl;
        state.num_solved_vars += 1;
        rst.update(RestarterModule::Reset, 0);
    } else {
        {
            // At the present time, some reason clauses can contain first UIP or its negation.
            // So we have to filter vars instead of literals to avoid double counting.
            let mut bumped = new_learnt.iter().map(|l| l.vi()).collect::<Vec<VarId>>();
            for lit in new_learnt.iter() {
                //
                //## Learnt Literal Rewarding
                //
                vdb.reward_at_analysis(lit.vi());
                if let AssignReason::Implication(r, _) = vdb[lit.vi()].reason {
                    for l in &cdb[r].lits {
                        let vi = l.vi();
                        if !bumped.contains(&vi) {
                            //
                            //## Reason-Side Rewarding
                            //
                            vdb.reward_at_analysis(vi);
                            bumped.push(vi);
                        }
                    }
                }
            }
        }
        asgs.cancel_until(vdb, bl);
        let cid = cdb.new_clause(asgs, new_learnt, Some(vdb));
        elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
        state.c_lvl.update(cl as f64);
        state.b_lvl.update(bl as f64);
        asgs.assign_by_implication(
            vdb,
            l0,
            AssignReason::Implication(
                cid,
                if learnt_len == 2 {
                    new_learnt[1]
                } else {
                    NULL_LIT
                },
            ),
            al,
        );
        let lbd = cdb[cid].rank;
        rst.update(RestarterModule::LBD, lbd);
        if learnt_len < 8 {
            state.to_eliminate += std::f64::consts::E.powf(-(learnt_len as f64));
        }
    }
    cdb.scale_activity();
    if 0 < state.config.dump_int && ncnfl % state.config.dump_int == 0 {
        let (_mode, rst_num_block, rst_asg_trend, _lbd_get, rst_lbd_trend) = rst.exports();
        state.development.push((
            ncnfl,
            (state.num_solved_vars + state.num_eliminated_vars) as f64
                / state.target.num_of_variables as f64,
            asgs_num_restart as f64,
            rst_num_block as f64,
            rst_asg_trend.min(10.0),
            rst_lbd_trend.min(10.0),
        ));
    }
    cdb.check_and_reduce(vdb, ncnfl);
    if ncnfl % state.reflection_interval == 0 {
        adapt_modules(asgs, cdb, elim, rst, state, vdb)?;
        if let Some(p) = state.elapsed() {
            if 1.0 <= p {
                return Err(SolverError::TimeOut);
            }
        } else {
            return Err(SolverError::UndescribedError);
        }
    }
    Ok(())
}

fn adapt_modules(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    vdb: &mut VarDB,
) -> MaybeInconsistent {
    state.progress(asgs, cdb, elim, rst, vdb, None);
    let (asgs_num_conflict, _num_propagation, _num_restart) = asgs.exports();
    if 10 * state.reflection_interval == asgs_num_conflict {
        // Need to call it before `cdb.adapt_to`
        // 'decision_level == 0' is required by `cdb.adapt_to`.
        asgs.cancel_until(vdb, state.root_level);
        state.select_strategy(asgs, cdb);
        // if state.strategy.0 == SearchStrategy::HighSuccesive {
        //     state.config.cbt_thr = 0;
        // }
    }
    #[cfg(feature = "boundary_check")]
    assert!(state.strategy.1 != asgs_num_conflict || 0 == asgs.level());
    cdb.adapt_to(state, asgs_num_conflict);
    rst.adapt_to(state, asgs_num_conflict);
    vdb.adapt_to(state, asgs_num_conflict);
    state.phase_select = match (asgs_num_conflict / state.reflection_interval) % 2 {
        0 => PhaseMode::BestRnd,
        _ => PhaseMode::Latest,
    };
    Ok(())
}

///
/// ## Conflict Analysis
///
#[allow(clippy::cognitive_complexity)]
fn conflict_analyze(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
    confl: ClauseId,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asgs.level();
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    loop {
        let reason = if p == NULL_LIT {
            AssignReason::Implication(confl, NULL_LIT)
        } else {
            vdb[p.vi()].reason
        };
        match reason {
            AssignReason::None => panic!("here"),
            AssignReason::Implication(_, l) if l != NULL_LIT => {
                // cid = vdb[p.vi()].reason;
                let vi = l.vi();
                if !vdb[vi].is(Flag::CA_SEEN) {
                    let lvl = asgs.level_ref()[vi];
                    let v = &mut vdb[vi];
                    if 0 == lvl {
                        continue;
                    }
                    debug_assert!(!v.is(Flag::ELIMINATED));
                    debug_assert!(v.assign.is_some());
                    v.turn_on(Flag::CA_SEEN);
                    if dl <= lvl {
                        path_cnt += 1;
                        vdb.reward_at_analysis(vi);
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        println!("- push {} to learnt, which level is {}", q.int(), lvl);
                        // learnt.push(l);
                    }
                } else {
                    #[cfg(feature = "trace_analysis")]
                    {
                        if !v.is(Flag::CA_SEEN) {
                            println!("- ignore {} because it was flagged", q.int());
                        } else {
                            println!("- ignore {} because its level is {}", q.int(), lvl);
                        }
                    }
                }
            }
            AssignReason::Implication(cid, _) => {
                #[cfg(feature = "trace_analysis")]
                println!("analyze {}", p.int());
                debug_assert_ne!(cid, ClauseId::default());
                if cdb[cid].is(Flag::LEARNT) {
                    if !cdb[cid].is(Flag::JUST_USED) && !cdb.convert_to_permanent(asgs, cid) {
                        cdb[cid].turn_on(Flag::JUST_USED);
                    }
                    cdb.bump_activity(cid, ());
                }
                let c = &cdb[cid];
                #[cfg(feature = "boundary_check")]
                assert!(
                    0 < c.len(),
                    format!(
                        "Level {} I-graph reaches {}:{} for {}:{}",
                        asgs.level(),
                        cid,
                        c,
                        p,
                        &vdb[p]
                    )
                );
                #[cfg(feature = "trace_analysis")]
                println!("- handle {}", cid.fmt());
                for q in &c[(p != NULL_LIT) as usize..] {
                    let vi = q.vi();
                    if !vdb[vi].is(Flag::CA_SEEN) {
                        // vdb.reward_at_analysis(vi);
                        let lvl = asgs.level_ref()[vi];
                        let v = &mut vdb[vi];
                        if 0 == lvl {
                            continue;
                        }
                        debug_assert!(!v.is(Flag::ELIMINATED));
                        debug_assert!(v.assign.is_some());
                        v.turn_on(Flag::CA_SEEN);
                        if dl <= lvl {
                            // println!("- flag for {} which level is {}", q.int(), lvl);
                            path_cnt += 1;
                            //
                            //## Conflict-Side Rewarding
                            //
                            vdb.reward_at_analysis(vi);
                        } else {
                            #[cfg(feature = "trace_analysis")]
                            println!("- push {} to learnt, which level is {}", q.int(), lvl);
                            learnt.push(*q);
                        }
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        {
                            if !v.is(Flag::CA_SEEN) {
                                println!("- ignore {} because it was flagged", q.int());
                            } else {
                                println!("- ignore {} because its level is {}", q.int(), lvl);
                            }
                        }
                    }
                }
            }
        }
        // The following case was subsumed into `search`.
        /*
        // In an unsat problem, a conflict can occur at decision level zero
        // by a clause which literals' levels are zero.
        // So we have the posibility getting the following situation.
        if p == NULL_LIT && path_cnt == 0 {
            #[cfg(feature = "boundary_check")]
            println!("Empty learnt at lvl:{}", asgs.level());
            learnt.clear();
            return state.root_level;
        }
        */
        // set the index of the next literal to ti
        while {
            let vi = asgs[ti].vi();
            #[cfg(feature = "boundary_check")]
            assert!(
                vi < asgs.level_ref().len(),
                format!("ti:{}, lit:{}, len:{}", ti, asgs[ti], asgs.len(),)
            );
            let lvl = asgs.level_ref()[vi];
            let v = &vdb[vi];
            !v.is(Flag::CA_SEEN) || lvl != dl
        } {
            #[cfg(feature = "trace_analysis")]
            println!("- skip {} because it isn't flagged", asgs[ti].int());
            #[cfg(feature = "boundary_check")]
            assert!(
                0 < ti,
                format!(
                    "p:{}, path_cnt:{}, lv:{}, learnt:{:?}\nconflict:{:?}",
                    p,
                    path_cnt,
                    dl,
                    vdb.dump(asgs, &*learnt),
                    vdb.dump(asgs, &cdb[confl].lits),
                ),
            );
            ti -= 1;
        }
        p = asgs[ti];
        #[cfg(feature = "trace_analysis")]
        println!(
            "- move to flagged {}, which reason is {}; num path: {}",
            p.vi(),
            path_cnt - 1,
            cid.fmt()
        );
        vdb[p].turn_off(Flag::CA_SEEN);
        // since the trail can contain a literal which level is under `dl` after
        // the `dl`-th thdecision var, we must skip it.
        path_cnt -= 1;
        if path_cnt == 0 {
            break;
        }
        debug_assert!(0 < ti);
        ti -= 1;
    }
    debug_assert!(learnt.iter().all(|l| *l != !p));
    debug_assert_eq!(asgs.level_ref()[p.vi()], dl);
    learnt[0] = !p;
    #[cfg(feature = "trace_analysis")]
    println!(
        "- appending {}, the result is {:?}",
        learnt[0].int(),
        vec2int(learnt)
    );
    state.minimize_learnt(asgs, cdb, vdb)
}

impl Solver {
    fn inject(mut self, mut reader: BufReader<File>) -> Result<Solver, SolverError> {
        let mut buf = String::new();
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_) if buf.starts_with('c') => continue,
                Ok(_) => {
                    let iter = buf.split_whitespace();
                    let mut v: Vec<Lit> = Vec::new();
                    for s in iter {
                        match s.parse::<i32>() {
                            Ok(0) => break,
                            Ok(val) => v.push(Lit::from(val)),
                            Err(_) => (),
                        }
                    }
                    if !v.is_empty() && self.add_unchecked_clause(&mut v).is_none() {
                        return Err(SolverError::Inconsistent);
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(self.vdb.len() - 1, self.state.target.num_of_variables);
        // s.state[Stat::NumBin] = s.cdb.iter().skip(1).filter(|c| c.len() == 2).count();
        self.vdb.adapt_to(&self.state, 0);
        self.rst.adapt_to(&self.state, 0);
        Ok(self)
    }
}

impl State {
    fn minimize_learnt(
        &mut self,
        asgs: &AssignStack,
        cdb: &ClauseDB,
        vdb: &mut VarDB,
    ) -> DecisionLevel {
        let State {
            ref mut new_learnt, ..
        } = self;
        let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
        let mut levels = vec![false; asgs.level() as usize + 1];
        let level = asgs.level_ref();
        for l in &new_learnt[1..] {
            to_clear.push(*l);
            levels[level[l.vi()] as usize] = true;
        }
        let l0 = new_learnt[0];
        #[cfg(feature = "boundary_check")]
        assert!(0 < new_learnt.len());
        new_learnt.retain(|l| *l == l0 || !l.is_redundant(asgs, cdb, vdb, &mut to_clear, &levels));
        let len = new_learnt.len();
        if 2 < len && len < 30 {
            vdb.minimize_with_biclauses(cdb, new_learnt);
        }
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        let level = asgs.level_ref();
        if 1 < new_learnt.len() {
            let mut max_i = 1;
            level_to_return = level[new_learnt[max_i].vi()];
            for (i, l) in new_learnt.iter().enumerate().skip(2) {
                let lv = level[l.vi()];
                if level_to_return < lv {
                    level_to_return = lv;
                    max_i = i;
                }
            }
            new_learnt.swap(1, max_i);
        }
        for l in &to_clear {
            vdb[l].turn_off(Flag::CA_SEEN);
        }
        level_to_return
    }
}

/// return `true` if the `lit` is redundant, which is defined by
/// any leaf of implication graph for it isn't a fixed var nor a decision var.
impl Lit {
    fn is_redundant(
        self,
        asgs: &AssignStack,
        cdb: &ClauseDB,
        vdb: &mut VarDB,
        clear: &mut Vec<Lit>,
        levels: &[bool],
    ) -> bool {
        if vdb[self].reason == AssignReason::default() {
            return false;
        }
        let mut stack = Vec::new();
        stack.push(self);
        let top = clear.len();
        let level = asgs.level_ref();
        while let Some(sl) = stack.pop() {
            match vdb[sl.vi()].reason {
                AssignReason::None => panic!("no idea"),
                AssignReason::Implication(_, l) if l != NULL_LIT => {
                    let vi = l.vi();
                    let lv = level[vi];
                    let v = &mut vdb[vi];
                    if 0 < lv && !v.is(Flag::CA_SEEN) {
                        if v.reason != AssignReason::default() && levels[lv as usize] {
                            v.turn_on(Flag::CA_SEEN);
                            stack.push(l);
                            clear.push(l);
                        } else {
                            // one of the roots is a decision var at an unchecked level.
                            for l in &clear[top..] {
                                vdb[l.vi()].turn_off(Flag::CA_SEEN);
                            }
                            clear.truncate(top);
                            return false;
                        }
                    }
                }
                AssignReason::Implication(cid, _) => {
                    let c = &cdb[cid];
                    #[cfg(feature = "boundary_check")]
                    assert!(0 < c.len());
                    for q in &(*c)[1..] {
                        let vi = q.vi();
                        let lv = level[vi];
                        let v = &mut vdb[vi];
                        if 0 < lv && !v.is(Flag::CA_SEEN) {
                            if v.reason != AssignReason::default() && levels[lv as usize] {
                                v.turn_on(Flag::CA_SEEN);
                                stack.push(*q);
                                clear.push(*q);
                            } else {
                                // one of the roots is a decision var at an unchecked level.
                                for l in &clear[top..] {
                                    vdb[l.vi()].turn_off(Flag::CA_SEEN);
                                }
                                clear.truncate(top);
                                return false;
                            }
                        }
                    }
                }
            }
        }
        true
    }
}

fn analyze_final(asgs: &AssignStack, state: &mut State, vdb: &mut VarDB, c: &Clause) {
    let mut seen = vec![false; state.num_vars + 1];
    state.conflicts.clear();
    if asgs.level() == 0 {
        return;
    }
    for l in &c.lits {
        let vi = l.vi();
        if 0 < asgs.level_ref()[vi] {
            vdb[vi].turn_on(Flag::CA_SEEN);
        }
    }
    let end = if asgs.level() <= state.root_level {
        asgs.len()
    } else {
        asgs.len_upto(state.root_level)
    };
    for l in &asgs[asgs.len_upto(0)..end] {
        let vi = l.vi();
        if seen[vi] {
            if vdb[vi].reason == AssignReason::default() {
                state.conflicts.push(!*l);
            } else {
                let level = asgs.level_ref();
                for l in &c[(c.len() != 2) as usize..] {
                    let vj = l.vi();
                    if 0 < level[vj] {
                        seen[vj] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
}

#[allow(dead_code)]
impl VarDB {
    fn dump<'a, A, V: IntoIterator<Item = &'a Lit, IntoIter = Iter<'a, Lit>>>(
        &mut self,
        asgs: &A,
        v: V,
    ) -> Vec<(i32, DecisionLevel, bool, Option<bool>)>
    where
        A: AssignIF,
    {
        v.into_iter()
            .map(|l| {
                let lvl = asgs.level_ref()[l.vi()];
                let v = &self[*l];
                (
                    i32::from(l),
                    lvl,
                    v.reason == AssignReason::default(),
                    v.assign,
                )
            })
            .collect::<Vec<(i32, DecisionLevel, bool, Option<bool>)>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_solver() {
        let config = Config::from("tests/sample.cnf");
        if let Ok(s) = Solver::build(&config) {
            assert_eq!(s.state.num_vars, 250);
            assert_eq!(s.state.num_unsolved_vars(), 250);
        } else {
            panic!("failed to build a solver for tests/sample.cnf");
        }
    }
}
