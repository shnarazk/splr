/// Crate 'solver' provides the top-level API as a SAT solver.
use {
    crate::{
        assign::{AssignIF, AssignStack, VarRewardIF, VarSelectionIF},
        clause::{ClauseDB, ClauseDBIF},
        eliminate::{EliminateIF, Eliminator},
        restart::{RestartIF, RestartMode, Restarter, RestarterModule},
        state::{PhaseMode, Stat, State, StateIF},
        types::*,
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
    pub asg: AssignStack,
    /// clause container
    pub cdb: ClauseDB,
    /// clause and variable elimination
    pub elim: Eliminator,
    /// restart management
    pub rst: Restarter,
    /// misc data holder
    pub state: State,
}

impl Default for Solver {
    fn default() -> Solver {
        Solver {
            asg: AssignStack::default(),
            cdb: ClauseDB::default(),
            elim: Eliminator::default(),
            rst: Restarter::instantiate(&Config::default(), &CNFDescription::default()),
            state: State::default(),
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
            asg: AssignStack::instantiate(config, cnf),
            cdb: ClauseDB::instantiate(config, cnf),
            elim: Eliminator::instantiate(config, cnf),
            rst: Restarter::instantiate(config, &cnf),
            state: State::instantiate(config, cnf),
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
    ($asg: expr, $cdb: expr, $elim: expr, $rst: expr, $state: expr) => {
        let c = $state.config.no_color;
        let q = $state.config.quiet_mode;
        $state.config.no_color = true;
        $state.config.quiet_mode = false;
        if q {
            $state.progress_header();
        }
        $state.progress($asg, $cdb, $elim, $rst, None);
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
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ref mut rst,
            ref mut state,
        } = self;
        if cdb.check_size().is_err() {
            return Err(SolverError::OutOfMemory);
        }
        // NOTE: splr doesn't deal with assumptions.
        // s.root_level = 0;
        state.num_solved_vars = asg.stack_len();
        state.progress_header();
        state.progress(asg, cdb, elim, rst, Some("initialization phase"));
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
        elim.prepare(asg, cdb, true);
        for vi in 1..=state.num_vars {
            if asg.assign(vi).is_some() {
                continue;
            }
            match elim.stats(vi) {
                (_, 0) => {
                    let l = Lit::from_assign(vi, true);
                    if asg.assign_at_rootlevel(l).is_err() {
                        return Ok(Certificate::UNSAT);
                    }
                }
                (0, _) => {
                    let l = Lit::from_assign(vi, false);
                    if asg.assign_at_rootlevel(l).is_err() {
                        return Ok(Certificate::UNSAT);
                    }
                }
                (p, m) => {
                    asg.var_mut(vi).set(Flag::PHASE, m < p);
                    elim.enqueue_var(asg, vi, false);
                }
            }
        }
        //
        //## Run eliminator
        //
        if !USE_PRE_PROCESSING_ELIMINATOR || !elim.enable {
            elim.stop(asg, cdb);
        }
        if USE_PRE_PROCESSING_ELIMINATOR && elim.enable {
            state.flush("simplifying...");
            // if 20_000_000 < state.target.num_of_clauses {
            //     state.elim_eliminate_grow_limit = 0;
            //     state.elim_eliminate_loop_limit = 1_000_000;
            //     state.elim_subsume_loop_limit = 2_000_000;
            // }
            if elim.simplify(asg, cdb, state).is_err() {
                // Why inconsistent? Because the CNF contains a conflict, not an error!
                // Or out of memory.
                final_report!(asg, cdb, elim, rst, state);
                if cdb.check_size().is_err() {
                    return Err(SolverError::OutOfMemory);
                }
                return Ok(Certificate::UNSAT);
            }
            for vi in 1..=state.num_vars {
                if asg.assign(vi).is_some() || asg.var(vi).is(Flag::ELIMINATED) {
                    continue;
                }
                match elim.stats(vi) {
                    (_, 0) => (),
                    (0, _) => (),
                    (p, m) if m * 10 < p => asg.var_mut(vi).turn_on(Flag::PHASE),
                    (p, m) if p * 10 < m => asg.var_mut(vi).turn_off(Flag::PHASE),
                    _ => (),
                }
            }
            asg.initialize_reward(elim.sorted_iterator());
        }
        asg.rebuild_order();
        state.progress(asg, cdb, elim, rst, None);

        //
        //## Search
        //
        let answer = search(asg, cdb, elim, rst, state);
        final_report!(asg, cdb, elim, rst, state);
        match answer {
            Ok(true) => {
                asg.extend_model(elim.eliminated_lits());
                #[cfg(debug)]
                {
                    if let Some(cid) = cdb.validate(vdb, true) {
                        panic!(
                            "Level {} generated assignment({:?}) falsifies {}:{:?}",
                            asg.level(),
                            cdb.validate(vdb, false).is_none(),
                            cid,
                            vdb.dump(asg, &cdb[cid]),
                        );
                    }
                }
                if cdb.validate(asg, true).is_some() {
                    return Err(SolverError::SolverBug);
                }
                let vals = asg
                    .var_iter()
                    .skip(1)
                    .map(|v| i32::from(Lit::from((v.index, asg.assign(v.index)))))
                    .collect::<Vec<i32>>();
                asg.cancel_until(state.root_level);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::NullLearnt) => {
                asg.cancel_until(state.root_level);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                asg.cancel_until(state.root_level);
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
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ..
        } = self;
        if lits.is_empty() {
            return None;
        }
        debug_assert!(asg.decision_level() == 0);
        if lits.iter().any(|l| asg.assigned(*l).is_some()) {
            cdb.certificate_add(lits);
        }
        lits.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means tautology.
        for i in 0..lits.len() {
            let li = lits[i];
            let sat = asg.assigned(li);
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
            1 => asg
                .assign_at_rootlevel(lits[0])
                .map_or(None, |_| Some(ClauseId::default())),
            _ => {
                let cid = cdb.new_clause(asg, lits, false, false);
                elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
                Some(cid)
            }
        }
    }
}

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
#[inline]
fn search(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
) -> Result<bool, SolverError> {
    let mut a_decision_was_made = false;
    let mut num_assigned = (0, 0); // (best, target)
    let mut nap = &mut num_assigned.0;
    let phasing_duration = state.reflection_interval / 5;
    let mut select_phase: usize = phasing_duration;
    let mut stabilizing = if rst.exports().0 == RestartMode::Stabilize {
        Flag::TARGET_PHASE
    } else {
        Flag::BEST_PHASE
    };
    rst.update(RestarterModule::Luby, 0);
    loop {
        asg.reward_update();
        let ci = asg.propagate(cdb);
        if ci == ClauseId::default() {
            if state.num_vars <= asg.stack_len() + state.num_eliminated_vars {
                return Ok(true);
            }

            //
            //## DYNAMIC FORCING RESTART based on LBD values, updated by conflict
            //
            state.last_asg = asg.stack_len();
            if rst.force_restart() {
                asg.cancel_until(state.root_level);
            } else {
                //
                //## set phase mode
                //
                stabilizing = if rst.exports().0 == RestartMode::Stabilize {
                    if stabilizing != Flag::TARGET_PHASE {
                        asg.reset_assign_record(Flag::TARGET_PHASE, Some(Flag::BEST_PHASE));
                    }
                    nap = &mut num_assigned.1;
                    Flag::TARGET_PHASE
                } else {
                    if num_assigned.0 < num_assigned.1 {
                        num_assigned.0 = num_assigned.1;
                        asg.reset_assign_record(Flag::BEST_PHASE, Some(Flag::TARGET_PHASE));
                    }
                    nap = &mut num_assigned.0;
                    Flag::BEST_PHASE
                };
            }
            let mut na = asg.best_assigned(stabilizing);
            if 0 < na {
                na += state.num_eliminated_vars;
                if *nap < na {
                    *nap = na;
                    state.flush("");
                    state.flush(format!("find best assigns: {}", na));
                    state.phase_select = PhaseMode::Best;
                }
            }
        //
        } else {
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NoDecisionConflict] += 1;
            }
            if asg.decision_level() == state.root_level {
                analyze_final(asg, state, &cdb[ci]);
                return Ok(false);
            }
            handle_conflict(asg, cdb, elim, rst, state, ci)?;

            let asg_num_conflict = asg.exports().0;
            if select_phase == 0 {
                select_phase = phasing_duration;
                state.phase_select = if rst.exports().0 == RestartMode::Stabilize {
                    match asg_num_conflict % 3 {
                        // _ if rst.exports().0 == RestartMode::Stabilize => PhaseMode::BestRnd,
                        // 0 if state.phase_select == PhaseMode::Latest => PhaseMode::Best,
                        // 0 => PhaseMode::Best,
                        1 => PhaseMode::Best,
                        // 2 => PhaseMode::Random,
                        _ => PhaseMode::Target,
                    }
                } else {
                    match asg_num_conflict % 8 {
                        // 0 => PhaseMode::Best,
                        3 => PhaseMode::Invert,
                        // 6 => PhaseMode::Target,
                        // 6 => PhaseMode::Random,
                        _ => PhaseMode::Latest,
                    }
                };
            } else {
                select_phase -= 1;
            }
        }
        // Simplification has been postponed because chronoBT was used.
        if asg.decision_level() == state.root_level {
            // `elim.to_eliminate` is increased much in particular when vars are solved or
            // learnts are small. We don't need to count the number of solved vars.
            if state.config.elim_trigger < state.to_eliminate as usize {
                state.to_eliminate = 0.0;
                if elim.enable {
                    elim.activate();
                }
                elim.simplify(asg, cdb, state)?;
            }
            // By simplification, we may get further solutions.
            if state.num_solved_vars < asg.stack_len() {
                rst.update(RestarterModule::Reset, 0);
                state.num_solved_vars = asg.stack_len();
            }
        }
        if !asg.remains() {
            let vi = asg.select_var();
            let num_prop = asg.exports().1;
            let p = match state.phase_select {
                PhaseMode::Best => asg.var(vi).is(Flag::BEST_PHASE),
                PhaseMode::BestRnd => match num_prop % 8 {
                    0 => num_prop % 16 == 0,
                    4 => asg.var(vi).is(Flag::PHASE),
                    _ => asg.var(vi).is(stabilizing),
                },
                PhaseMode::Invert => !asg.var(vi).is(Flag::PHASE),
                PhaseMode::Latest => asg.var(vi).is(Flag::PHASE),
                PhaseMode::Random => num_prop % 2 == 0,
                PhaseMode::Target => asg.var(vi).is(Flag::TARGET_PHASE),
            };
            asg.assign_by_decision(Lit::from_assign(vi, p));
            state[Stat::Decision] += 1;
            a_decision_was_made = true;
        }
    }
}

#[allow(clippy::cognitive_complexity)]
#[inline]
fn handle_conflict(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    ci: ClauseId,
) -> MaybeInconsistent {
    const ELIMINATABLE: usize = 4;
    // we need a catch here for handling the possibility of level zero conflict
    // at higher level due to the incoherence between the current level and conflicting
    // level in chronoBT. This leads to UNSAT solution. No need to update misc stats.
    {
        let level = asg.level_ref();
        if cdb[ci].iter().all(|l| level[l.vi()] == 0) {
            return Err(SolverError::NullLearnt);
        }
    }

    let (ncnfl, _num_propagation, asg_num_restart, _, _) = asg.exports();
    // If we can settle this conflict w/o restart, solver will get a big progress.
    let switch_chronobt = if ncnfl < 1000 || asg.recurrent_conflicts() {
        Some(false)
    } else {
        None
    };
    rst.update(RestarterModule::Counter, ncnfl);

    if 0 < state.last_asg {
        rst.update(RestarterModule::ASG, asg.stack_len());
        state.last_asg = 0;
    }

    //
    //## DYNAMIC BLOCKING RESTART based on ASG, updated on conflict path
    //
    rst.block_restart();
    let cl = asg.decision_level();
    let mut use_chronobt = switch_chronobt.unwrap_or(0 < state.config.cbt_thr);
    if use_chronobt {
        let level = asg.level_ref();
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
                asg.cancel_until(snd_l - 1);
                debug_assert!(
                    asg.stack_iter().all(|l| l.vi() != decision.vi()),
                    format!("lcnt == 1: level {}, snd level {}", cl, snd_l)
                );
                asg.assign_by_decision(decision);
                return Ok(());
            }
        }
    }
    // conflicting level
    // By mixing two restart modes, we must assume a conflicting level is under the current decision level,
    // even if `use_chronobt` is off, because `use_chronobt` is a flag for future behavior.
    let cl = {
        let cl = asg.decision_level();
        let c = &cdb[ci];
        let level = asg.level_ref();
        let lv = c.iter().map(|l| level[l.vi()]).max().unwrap_or(0);
        if lv < cl {
            asg.cancel_until(lv);
            lv
        } else {
            cl
        }
    };
    debug_assert!(
        cdb[ci].iter().any(|l| asg.level(l.vi()) == cl),
        format!(
            "use_{}: {:?}, {:?}",
            use_chronobt,
            cl,
            cdb[ci]
                .iter()
                .map(|l| (i32::from(*l), asg.level(l.vi())))
                .collect::<Vec<_>>(),
        )
    );
    // backtrack level by analyze
    let bl_a = conflict_analyze(asg, cdb, state, ci).max(state.root_level);
    if state.new_learnt.is_empty() {
        #[cfg(debug)]
        {
            println!(
                "empty learnt at {}({}) by {:?}",
                cl,
                asg.reason(asg.decision_vi(cl)) == ClauseId::default(),
                vdb.dump(asg, &cdb[ci]),
            );
        }
        return Err(SolverError::NullLearnt);
    }
    // vdb.bump_vars(asg, cdb, ci);
    let new_learnt = &mut state.new_learnt;
    let l0 = new_learnt[0];
    // assert: 0 < cl, which was checked already by new_learnt.is_empty().

    // NCB places firstUIP on level bl, while CB does it on level cl.
    // Therefore the condition to use CB is: activity(firstUIP) < activity(v(bl)).
    // PREMISE: 0 < bl, because asg.decision_vi accepts only non-zero values.
    use_chronobt &= switch_chronobt.unwrap_or(
        bl_a == 0
            || state.config.cbt_thr + bl_a <= cl
            || asg.activity(l0.vi()) < asg.activity(asg.decision_vi(bl_a)),
    );

    // (assign level, backtrack level)
    let (al, bl) = if use_chronobt {
        (
            {
                let level = asg.level_ref();
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
            asg.cancel_until(bl);
            debug_assert!(asg.stack_iter().all(|l| l.vi() != l0.vi()));
            asg.assign_by_implication(l0, AssignReason::default(), 0);
        } else {
            asg.assign_by_unitclause(l0);
        }
        state.last_solved = ncnfl;
        state.num_solved_vars += 1;
        state.to_eliminate *= 0.25;
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
                asg.reward_at_analysis(lit.vi());
                if let AssignReason::Implication(r, _) = asg.reason(lit.vi()) {
                    for l in &cdb[r].lits {
                        let vi = l.vi();
                        if !bumped.contains(&vi) {
                            //
                            //## Reason-Side Rewarding
                            //
                            asg.reward_at_analysis(vi);
                            bumped.push(vi);
                        }
                    }
                }
            }
        }
        asg.cancel_until(bl);
        let cid = cdb.new_clause(asg, new_learnt, true, true);
        elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
        state.c_lvl.update(cl as f64);
        state.b_lvl.update(bl as f64);
        asg.assign_by_implication(
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
        if learnt_len <= ELIMINATABLE {
            // state.to_eliminate += std::f64::consts::E.powi(-(learnt_len as i32));
            state.to_eliminate += match learnt_len {
                2 => 1.0,
                3 => 0.001,
                4 => 0.000_01,
                _ => 0.000_000_1,
            };
        }
    }
    cdb.scale_activity();
    if 0 < state.config.dump_int && ncnfl % state.config.dump_int == 0 {
        let (_mode, rst_num_block, rst_asg_trend, _lbd_get, rst_lbd_trend) = rst.exports();
        state.development.push((
            ncnfl,
            (state.num_solved_vars + state.num_eliminated_vars) as f64
                / state.target.num_of_variables as f64,
            asg_num_restart as f64,
            rst_num_block as f64,
            rst_asg_trend.min(10.0),
            rst_lbd_trend.min(10.0),
        ));
    }
    cdb.check_and_reduce(asg, ncnfl);
    if ncnfl % state.reflection_interval == 0 {
        adapt_modules(asg, cdb, elim, rst, state)?;
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
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
) -> MaybeInconsistent {
    state.progress(asg, cdb, elim, rst, None);
    let (asg_num_conflict, _num_propagation, _num_restart, _, _) = asg.exports();
    if 10 * state.reflection_interval == asg_num_conflict {
        // Need to call it before `cdb.adapt_to`
        // 'decision_level == 0' is required by `cdb.adapt_to`.
        asg.cancel_until(state.root_level);
        state.select_strategy(asg, cdb);
        // if state.strategy.0 == SearchStrategy::HighSuccesive {
        //     state.config.cbt_thr = 0;
        // }
    }
    #[cfg(feature = "boundary_check")]
    assert!(state.strategy.1 != asg_num_conflict || 0 == asg.decision_level());
    asg.adapt_to(state, asg_num_conflict);
    cdb.adapt_to(state, asg_num_conflict);
    rst.adapt_to(state, asg_num_conflict);
    Ok(())
}

///
/// ## Conflict Analysis
///
#[allow(clippy::cognitive_complexity)]
fn conflict_analyze(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    confl: ClauseId,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asg.decision_level();
    let mut p = NULL_LIT;
    let mut ti = asg.stack_len() - 1; // trail index
    let mut path_cnt = 0;
    loop {
        let reason = if p == NULL_LIT {
            AssignReason::Implication(confl, NULL_LIT)
        } else {
            asg.reason(p.vi())
        };
        match reason {
            AssignReason::None => panic!("here"),
            AssignReason::Implication(_, l) if l != NULL_LIT => {
                // cid = vdb[p.vi()].reason;
                let vi = l.vi();
                if !asg.var(vi).is(Flag::CA_SEEN) {
                    let lvl = asg.level(vi);
                    if 0 == lvl {
                        continue;
                    }
                    debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                    debug_assert!(asg.assign(vi).is_some());
                    asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                    if dl <= lvl {
                        path_cnt += 1;
                        asg.reward_at_analysis(vi);
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        println!("- push {} to learnt, which level is {}", q.int(), lvl);
                        // learnt.push(l);
                    }
                } else {
                    #[cfg(feature = "trace_analysis")]
                    {
                        if !asg.var(vi).is(Flag::CA_SEEN) {
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
                    if !cdb[cid].is(Flag::JUST_USED) && !cdb.convert_to_permanent(asg, cid) {
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
                        asg.decision_level(),
                        cid,
                        c,
                        p,
                        asg.var(p.vi())
                    )
                );
                #[cfg(feature = "trace_analysis")]
                println!("- handle {}", cid.fmt());
                for q in &c[(p != NULL_LIT) as usize..] {
                    let vi = q.vi();
                    if !asg.var(vi).is(Flag::CA_SEEN) {
                        // vdb.reward_at_analysis(vi);
                        let lvl = asg.level(vi);
                        if 0 == lvl {
                            continue;
                        }
                        debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                        debug_assert!(asg.assign(vi).is_some());
                        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                        if dl <= lvl {
                            // println!("- flag for {} which level is {}", q.int(), lvl);
                            path_cnt += 1;
                            //
                            //## Conflict-Side Rewarding
                            //
                            asg.reward_at_analysis(vi);
                        } else {
                            #[cfg(feature = "trace_analysis")]
                            println!("- push {} to learnt, which level is {}", q.int(), lvl);
                            learnt.push(*q);
                        }
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        {
                            if !asg.var(vi).is(Flag::CA_SEEN) {
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
            println!("Empty learnt at lvl:{}", asg.level());
            learnt.clear();
            return state.root_level;
        }
        */
        // set the index of the next literal to ti
        while {
            let vi = asg.stack(ti).vi();
            #[cfg(feature = "boundary_check")]
            assert!(
                vi < asg.level_ref().len(),
                format!("ti:{}, lit:{}, len:{}", ti, asg.stack(ti), asg.stack_len())
            );
            let lvl = asg.level(vi);
            let v = asg.var(vi);
            !v.is(Flag::CA_SEEN) || lvl != dl
        } {
            #[cfg(feature = "trace_analysis")]
            println!("- skip {} because it isn't flagged", asg[ti].int());
            #[cfg(feature = "boundary_check")]
            assert!(
                0 < ti,
                format!(
                    "p:{}, path_cnt:{}, lv:{}, learnt:{:?}\nconflict:{:?}",
                    p,
                    path_cnt,
                    dl,
                    asg.dump(&*learnt),
                    asg.dump(&cdb[confl].lits),
                ),
            );
            ti -= 1;
        }
        p = asg.stack(ti);
        #[cfg(feature = "trace_analysis")]
        println!(
            "- move to flagged {}, which reason is {}; num path: {}",
            p.vi(),
            path_cnt - 1,
            cid.fmt()
        );
        asg.var_mut(p.vi()).turn_off(Flag::CA_SEEN);
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
    debug_assert_eq!(asg.level(p.vi()), dl);
    learnt[0] = !p;
    #[cfg(feature = "trace_analysis")]
    println!(
        "- appending {}, the result is {:?}",
        learnt[0].int(),
        vec2int(learnt)
    );
    state.minimize_learnt(asg, cdb)
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
        debug_assert_eq!(self.asg.var_len() - 1, self.state.target.num_of_variables);
        // s.state[Stat::NumBin] = s.cdb.iter().skip(1).filter(|c| c.len() == 2).count();
        self.asg.adapt_to(&self.state, 0);
        self.rst.adapt_to(&self.state, 0);
        Ok(self)
    }
}

impl State {
    fn minimize_learnt(&mut self, asg: &mut AssignStack, cdb: &ClauseDB) -> DecisionLevel {
        let State {
            ref mut new_learnt, ..
        } = self;
        let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
        let mut levels = vec![false; asg.decision_level() as usize + 1];
        let level = asg.level_ref();
        for l in &new_learnt[1..] {
            to_clear.push(*l);
            levels[level[l.vi()] as usize] = true;
        }
        let l0 = new_learnt[0];
        #[cfg(feature = "boundary_check")]
        assert!(!new_learnt.is_empty());
        new_learnt.retain(|l| *l == l0 || !l.is_redundant(asg, cdb, &mut to_clear, &levels));
        let len = new_learnt.len();
        if 2 < len && len < 30 {
            asg.minimize_with_biclauses(cdb, new_learnt);
        }
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        let level = asg.level_ref();
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
            asg.var_mut(l.vi()).turn_off(Flag::CA_SEEN);
        }
        level_to_return
    }
}

/// return `true` if the `lit` is redundant, which is defined by
/// any leaf of implication graph for it isn't a fixed var nor a decision var.
impl Lit {
    fn is_redundant(
        self,
        asg: &mut AssignStack,
        cdb: &ClauseDB,
        clear: &mut Vec<Lit>,
        levels: &[bool],
    ) -> bool {
        if asg.reason(self.vi()) == AssignReason::default() {
            return false;
        }
        let mut stack = Vec::new();
        stack.push(self);
        let top = clear.len();
        while let Some(sl) = stack.pop() {
            match asg.reason(sl.vi()) {
                AssignReason::None => panic!("no idea"),
                AssignReason::Implication(_, l) if l != NULL_LIT => {
                    let vi = l.vi();
                    let lv = asg.level(vi);
                    if 0 < lv && !asg.var(vi).is(Flag::CA_SEEN) {
                        if asg.reason(vi) != AssignReason::default() && levels[lv as usize] {
                            asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                            stack.push(l);
                            clear.push(l);
                        } else {
                            // one of the roots is a decision var at an unchecked level.
                            for l in &clear[top..] {
                                asg.var_mut(l.vi()).turn_off(Flag::CA_SEEN);
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
                        let lv = asg.level(vi);
                        if 0 < lv && !asg.var(vi).is(Flag::CA_SEEN) {
                            if asg.reason(vi) != AssignReason::default() && levels[lv as usize] {
                                asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                                stack.push(*q);
                                clear.push(*q);
                            } else {
                                // one of the roots is a decision var at an unchecked level.
                                for l in &clear[top..] {
                                    asg.var_mut(l.vi()).turn_off(Flag::CA_SEEN);
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

fn analyze_final(asg: &mut AssignStack, state: &mut State, c: &Clause) {
    let mut seen = vec![false; state.num_vars + 1];
    state.conflicts.clear();
    if asg.decision_level() == 0 {
        return;
    }
    for l in &c.lits {
        let vi = l.vi();
        if 0 < asg.level(vi) {
            asg.var_mut(vi).turn_on(Flag::CA_SEEN);
        }
    }
    let end = if asg.decision_level() <= state.root_level {
        asg.stack_len()
    } else {
        asg.len_upto(state.root_level)
    };
    for l in asg.stack_range(asg.len_upto(0)..end) {
        let vi = l.vi();
        if seen[vi] {
            if asg.reason(vi) == AssignReason::default() {
                state.conflicts.push(!*l);
            } else {
                let level = asg.level_ref();
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
impl AssignStack {
    fn dump<'a, V: IntoIterator<Item = &'a Lit, IntoIter = Iter<'a, Lit>>>(
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
