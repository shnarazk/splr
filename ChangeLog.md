## 0.17.4, 2025-01-28

- Rename feature 'no_clause_elimination' to 'clause_elimination'
- Move ClauseIF to clause.rs
- Move ClauseDb to db.rs
- Move Var to var.rs
- Move AssignStack to stack.rs
- Move AssignStack::{assign, level, reason, reason_saved} to Var
- Fix to recycle dead clauses

## 0.17.3, 2024-03-26

- Resolve #232, an incorrect debug assertion

## 0.17.2, 2024-02-04

- Add feature `platform_wasm`

## 0.17.1, 2023-07-07

- Fix compilation errors with feature 'no_IO'

## 0.17.0, 2023-01-30

- (Breaking change) `Certificate::try_from` returns `Ok` values even if a given vector
  contains empty clauses. All expressions corresponding to valid CNFs should be
  converted to `Certificate` successfully. On the other hand, `Solver::try_from` still
  returns `SolverError::EmptyClause`. (#191, #196, #197)
- Add a new feature 'reward_annealing' (#187)
- Fix misc wrong calculations on Luby series and stage-cycle-segment model (#194)
- Fix build errors without feature 'trial_saving' or 'rephase' (#202, #205)
- clause reduction uses revised parameters matching a Luby series based parameter shifting
  model (#195)
- add feature 'two_mode_reduction'

## 0.16.3, 2022-09-16

- Fix another bug on `add_var` and `add_assignment` (#183)
- Re-organize cnf module

## 0.16.2, 2022-09-07

- (Breaking change) methods to read a file take `std::path::Path` instead of `&str`
- Re-implement feature 'incremental_solver' correctly
- Define feature 'no_clause_elimination' instead of 'clause_elimination', which is activated
  by feature 'incremental_solver' automatically

## 0.15.0, 2022-05-15

- Add `solver::StageManager`, which defines stages, cycles, and segments based on Luby series.
  - At the end of each stage, solver runs the following:
    - clause reduction
    - trail-saving reconfiguration
  - At the end of each cycle, solver runs the following:
    - clause vivification
    - var re-phasing
  - At the end of each segment, solver runs the following:
    - clause subsumption and var elimination
    - var activity rescaling
    - restart threshold reconfiguration
  - drop `solver::restart::GeometricStabilizer` and `solver::restart::ProgressLuby`
- `Restarter` was renamed to `RestartManager` and stored in `State` as `State::restart`.
- Glucose-like restart blocking scheme was substituted with a simple dynamics model.
- Drop feature 'Luby_stabilization'. It became essential.
- Drop feature 'Luby_restart'.
- Drop feature 'strategy_adaptation'

## 0.14.0, 2021-11-01

- Rust 2021 edition
- `ConflictContext` uses `AssignReason`
- add feature 'suppress_reason_chain' that suppresses reason sequences consisting of binary clauses
- split `Flag` to `FlagClause` and `FlagVar` to reduce memory footprint
- select vivification targets based on LBD shrinking rate and they are protected from clause reduction
- introduce `BinaryLinkDB` and `BinaryLinkList`
  - Splr becomes deterministic (or monotonous) solver again
  - (ClauseDBIF) rename `bi_clause_map` to `binary_links`
  - remove 'hashed_watch_cache'
  - remove `reregister_watch_cache`
  - remove `restore_detached_watch_cache`
  - remove `WatchCacheHash`
- fix panic by clause vivification on UNSAT problems
- `Lit` uses `NonZeroU32` instead of `u32`.

## 0.13.0, 2021-10-11

- implement trail saving as an alternative of chrono-BT with following extensions:
  - reason refinement based on LBD values
  - heap operation optimization
- dump UNSAT certificate less frequently

## 0.12.0, 2021-09-25

- reduce memory footprint
- disable chrono-BT by default: it still generates wrong UNSAT certificates.
- revise LRB var rewarding
  - LRB tick is changed to the length from assignment to unassignment
- revise clause rewarding
  - clause activity is calculated based on its LBD and var activities
- dynamic control of restart interval

## 0.11.0, 2021-08-17

- clause reduction and Luby stabilization share the trigger condition.
- remove feature "clause_reduction"; this is essential.
- reorganize restart stabilization
- revise clause vivifier, removing non-essential tweaks
- add an experimental feature "adjust_restart_parameters"

## 0.10.0, 2021-07-10

### Fix critical bugs
- fix bugs on chronoBT implementation, which have affected Splr from version 0.3.1 to 0.7.0.
   - `AssignStack::q_head` had a wrong index after backtrack if chronoBT was used.
   - Non-chronoBT was broken if the number of the highest literal in conflicting clauses is one.
- fix a bug which has been rarely occurred by eliminator.
   - `AssignIF::propagate` skipped clause-level satisfiability checking,
     if its `blocker` held an eliminated var, which was never falsified.
   - `ClauseDB::strengthen_by_elimination` didn't turn `LEARNT` off
     when a clause became binary.

### Incompatible API changes from 0.7.0
By introducing new data types, Splr-0.10 checks the status after calling destructive
functions more rigidly.

- introduce a new data `RefClause` for clause-level state transition
- `AssignReason` has 4 states
- define assign::property
- append AssignIF::dump_cnf
- define cdb::property
- ClauseDB exports reference iterators on watch_caches instead of mutable references to them
- ClauseDB exports new transform functions that encapsulate internal state transitions
- ClauseDB and Clause export only immutable references to literals in clauses.
- ClauseDB exports a new method set on a new certificate saver.
- append ClauseDB::strengthen_by_vivification
- remove ClauseDB::count
- remove ClauseDB::countf
- rename ClauseDB::detach to ClauseDB::remove_clause
- remove ClauseDB::garbage_collect
- rename ClauseDB::minimize_with_biclauses to minimize_with_bi_clauses
- remove ClauseDB::new_clause_sandbox
- remove ClauseDB::registered_biclause
- rename ClauseDB::strengthen to ClauseDB::strengthen_by_elimination
- remove ClauseDB::touch_var
- remove EliminateIF::add_cid_occur
- remove EliminateIF::remove_cid_occur
- remove EliminateIF::stop
- screen Eliminator's fields
- define processor::property
- define restart::property
- append SatSolverIF::save_certification
- append SatSolverIF::dump_cnf

### other changes

- ClauseId uses NonZeroU32 instead of u32.
- define feature 'trace_equivalency' for debugging
- define (but incomplete) feature 'support_user_assumption'
- activate feature 'clause_vivification' by default
- activate feature 'rephase' by default, which selects the best phases and its variants
- delete features 'var-boosting' and 'best_phases_reuse'
- rename feature 'ema_calibration' to 'EMA_calibration'
- remove comment lines from UNSAT certification files, which default name is changed to 'proof.drat'.
- var reward decay rate has a static value
- dump all stats data into answer files
- slim down */mod.rs
- all vars have a non-zero initial activity

## 0.7.0, 2021-03-14

- answer filenames start with "ans_" instead of ".ans_" by default.
- reorganize trait
  - replace {Export, ExportBox} with {PropertyDereference, PropertyReference}
  - remove: ClauseManipulationIF, EliminatorStatIF
  - export: Ema, Ema2, EmaIF, PropertyDereference, PropertyReference
  - make private: assign::VarOrderIF, processor::VarOrderIF
- reorganize features:
  - add:
    - best_phases_tracking
    - best_phases_reuse
    - clause_elimination
    - clause_reduction
    - clause_vivification
    - LR_rewarding
    - Luby_stabilization
    - reason_side_rewarding
    - var_staging
  - drop:
    - explore_timestamp
    - extra_var_reward
    - luby_blocking
    - moving_var_reward_rate (switching to stage-based reward decay increment)
    - progress_ACC
    - progress_MLD
    - pure_stabilization
  - rename feature use_luby to Luby_restart
- clause simplifier and clause vivifier are called at the ends of stages
- Learning Rate based var rewarding uses a non-linear weight function.
- Since Luby stabilization has long cycles, cycle-based tasks were organized. "Stage" is defined based on Luby-stabilization level. Updated terminology:
   - _Luby stabilization_ is a scheme that defines duration of stabilization modes based on Luby series.
   - Luby stabilization stage, or _stage_ is a span that shares a Luby value.
   - _cycle_ is a span between two highest values in Luby series.
   - _var boosting_ is to promote specific vars during a stage.
   - _boosted vars_ or _staged vars_ are the vars promoted by var boosting.
   - _rephrase_ is to promote specific literals during a stage.

## 0.6.3, 2021-02-12

- `Solver` and other structs implement `Clone`
- `VarRewardIF` was merged into `ActivityIF`. `ClauseDB` implements it.
- Learning-rate-based var rewarding uses the number of conflicts instead of the number of BCPs, which was not intended.
- switch to a one-restarting-after-blocking-N-restarts stabilizer
- switch to stabilization-mode-driven clause reduction, vivification, and simplification
- disable re-phasing and vivification by default
- recycle `Watch` data
- handle '--no-color' and '--quiet' correctly
- add command-line option: '--journal'

## 0.6.2, 2021-01-20

- update LBD correctly
- check CNF header correctly
- add command line option: --rse

## 0.6.1, 2021-01-16

- fix compilation errors on configurations with feature 'incremental_solver'
- fix a typo in README.md

## 0.6.0, 2021-01-16

- reorganize with redefined terminology
   - _stabilizing_ to stop restart periodically (extension of static restart blocking)
   - _staging_ to restrict search space by adding extra var activity
   - _rephasing_ to reuse a good assignment set (so it means 'rephasing to good phases').
- delete dependencies on 'libc' and 'structopt'
- make Splr deterministic or *monotonous*, by removing timer based decision makers. Monotonous means that if a solver solves a problem within T timeout, it solves the problem within any timeout longer than T.
- Solver::restart provides both of `restart` and `stabilize`
- fix a bug in chronoBT, that occurred if a conflicting clause has just a single literal at the conflicting level.
- revise command line option parser to handle the last option better
- stabilization span and restart blocking levels are controlled with Luby sequence
- add an extra reward to vars involved in best phase
- make the learning rate of var rewarding constant
- change the definition of restart blocker and its default threshold
- add or modify command line options: --srd, --srv, --vbd, --vbr
- change the definitions or the default values: --rat, --rlt
- delete command line options: --rct, --rms, --rmt, --vri, --vrm, --vro

#### Verification

- all the certifications of [UUF250](https://github.com/shnarazk/SAT-bench/tree/master/3-SAT/UUF250) were correct and verified with [Grad](https://www21.in.tum.de/~lammich/grat/).
- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip) -- splr-0.6.0 RC() solved with a 300 sec (soft) timeout:
  - 45 (20201226), 42 (eab832c), and 38 (0.6.0) satisfiable problems: all the solutions were correct.
  - 6 (20201226), 4 (eab832c), and 4 (0.6.0) unsatisfiable problems: all the certifications were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![Benchmark result(2021-01-16)](https://user-images.githubusercontent.com/997855/104808677-24d97080-582b-11eb-85af-d01fd161bafd.png)

![Benchmark result(2020-12-27)](https://user-images.githubusercontent.com/997855/103163156-9f6f2b80-483d-11eb-90d3-29d076792c13.png)

## 0.5.0, 2020-08-30

- massive changes on the default parameters about restart
  - restart condition was revised as a multi-armed bandid problem
  - add some new criteria which are not documented yet
- compute LBD of permanent clauses correctly
- implement clause vivification
- add `ClauseDB::bin_watcher`
- delete `Watch::binary`
- `ClauseDB::new_clause` takes `&mut Vec<Lit>` instead of `&mut [Lit]`
- substitute copying literals with `std::mem::swap` in `ClauseDB::new_clause`
- stop sorting literals in `ClauseDB::new_clause`
- fix the certification symbol used by removing clauses
- fix a wrong initial value for `Config::rst_lbd_thr` which should be larger than 1.0
- revise the timeout for pre-processor

#### Verification

- all the certifications of [UUF250](https://github.com/shnarazk/SAT-bench/tree/master/3-SAT/UUF250) were correct and verified with [Grad](https://www21.in.tum.de/~lammich/grat/).
- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip) -- splr-0.5.0(3e68efc) solved with a 500 sec (soft) timeout:
  - 67 satisfiable problems: all the solutions were correct.
  - 7 unsatisfiable problems: all the certifications were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![](https://user-images.githubusercontent.com/997855/91648473-42d44d80-eaa3-11ea-83d8-5a52e02621d0.png)

## 0.4.1, 2020-05-28

- the installation command is changed to `cargo install splr --features cli`
- add feature "incremental_solver" providing `SatSolverIF::{add_assign, add_var, reset}` and `Solver::iter` and delete some old features
- `cargo build --lib` doesn't depend on 'libc', 'structopt' and 'time' anymore; Splr can be compiled to WASM
- `--quiet` option stops progress report completely
- a tiny modification on var selection heuristics
- squash git history on the master branch

#### Verification

- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip), splr-0.4.1(be30d17, 7064c9) solved with a 400 sec (soft) timeout:
  - 48 satisfiable problems: all the solutions were correct.
  - 7 unsatisfiable problems: all were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![](https://user-images.githubusercontent.com/997855/82614843-c14b6480-9c03-11ea-9fe9-1a4d367d7290.png)

## 0.4.0, 2020-05-06

- change a lot of options' meanings and mnemonics
- adapt to the output format defined in chapter 5 of [SAT competition 2011 rules](http://www.satcompetition.org/2011/rules.pdf)
- remove code about 'deep search' completely, superseded with stabilizing mode
- implement a simple re-phase mechanism
- implement `TryFrom<Vec<Vec<i32>>> for {Certificate, Solver}` for on-memory solving
- add features for development: boundary_check, EVSIDS, trace_analysis, no_IO
- better modularity and abstraction via traits and sub-modules
- catch a rare crash case in `conflict_analyze`
- `propagate` skips up to the last position; `propagate` skips up to the last position
- change the activation timings of simplification
- stop *too* dynamic var decay control
- activate `JUST_USED` for clause reduction
- stats data are stored in each module

#### Verification

- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip), splr-0.4.0(e0461bd) solved with a 300 sec (soft) timeout:
  - 43 satisfiable problems: all the solutions were correct.
  - 4 unsatisfiable problems: all were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![](https://user-images.githubusercontent.com/997855/81140412-32eca700-8fa4-11ea-9067-8369fba31c6b.png)

## 0.3.2, 2020-03-20

- control var activity decay rate based on the number of hot vars
- set var activity parameters for each search strategy correctly
- move `Clause::simplify` to `Eliminator` and make `Eliminator::eliminate` private
- make `Var` smaller
- define `DecisionLevel`
- generate a result file even if splr failed to solve
- define `restarter` as the sixth module of `Solver`
- add `--quiet` mode to show only the last stats

## 0.3.1, 2020-02-22

- adopt Chronological Backtrack; A. Nadel and V. Ryvchin: Chronological Backtracking, *Theory and Applications of Satisfiability Testing - SAT 2018*, pp.111–121, 2018.
- dmcr enables colorized output
- update options
  - add --chronoBT
  - delete --without-deep-search
  - rename --without-adaptive-strategy to --no-adaptive-strategy
- stop using deep-search mode
- revise validation framework: ClauseDBIF::validate, VarDBIF::status
- add SolverError::{NullLearnt, SolverBug}
- implement IntoIterator for {AssignStack, Clause}

#### Verification

- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip), splr-0.3.1 solved with a 200 sec (soft) timeout:
  - 35 satisfiable problems: all the solutions were correct.
  - 4 unsatisfiable problems:
    - 3 were verified with Grad.
    - Verifying gto_p60c238-sc2018.cnf was timed out due to the size of the drat file (1.3 GB).

## 0.3.0, 2020-02-10

- remove src/traits.rs and revise traits:
  - ActivityIF
  - EliminatorIF
  - EmaIF
  - LBDIF
  - LitIF
  - PropagatorIF
  - StateIF
  - VarDBIF
  - VarRewardIF
  - VarSelectionIF
- adopt learning rate based branch with with reason side rewarding
- better decay parameters
- better tests in src/\*.rs
- drop adaptive_restart
- add more ProgressEvaluators
- implement Index and IndexMut traits for several structs
- AssignStack::propagate normalizes flipped binary clauses to reduce computational cost in conflict analysis
- make deep_search sporadic
- revise output format; the last line contains only satisfiability and filename
- use another parameter set for giant problems
- set the default value of timeout to 10000 instead of 0

## 0.2.1, 2019-12-17

- redefine `ClauseId` as a struct

## 0.2.0, 2019-11-29

- redefine `Lit` as a struct with some standard traits

## 0.1.5, 2019-10-29

- adopt a modified CHB instead of EVSIDS
- introduce [big bang initialization](https://medium.com/backjump-technologies/big-bang-initialization-of-variable-activity-in-a-sat-solver-ada154f56fb0) for variable activity
- The literal encoding uses even integers for positive literals
- `Lbool` was changed to `Option<bool>`

## 0.1.4, 2019-09-12

- fix wrong computations about `State::{c_lvl, b_lvl}`, `Clause::activity`
- add '--stat' option to dump a history of internal state
- add new structs for better modularity: `ProgressEvaluator`, `RestartExecutor`, `VarDB`

## 0.1.3, 2019-05-07

- a tiny pack of updates on restart parameters and command line options

## 0.1.2, 2019-03-07

- various changes on heuristic adaptation, restart, and clause/variable elimination modules
- use CPU time if available
- More command line options were added.

## 0.1.1, 2019-02-23

- `splr --certify` generates DRAT, certificates of unsatisfiability.
- Clause id was changed from u64 to u32.
- The answer file format was slightly modified.
- Some command line options were changed.

## 0.1.0, 2019-02-14

- Answers were verified with Glucose and Lingeling.

#### Verification

- The first 100 problems from
  [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html),
  [250 variables uniform random satisfiable 3-SAT](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf250-1065.tar.gz)
  : all the solutions were correct.
- The first 100 problems from
  [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html),
  [250 variables uniform random unsatisfiable 3-SAT](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf250-1065.tar.gz)
  : all the solutions were correct and verified with [drat-trim](http://www.cs.utexas.edu/~marijn/drat-trim/).
- [SAT Competition 2017](https://baldur.iti.kit.edu/sat-competition-2017/index.php?cat=tracks),
  [Main track](https://baldur.iti.kit.edu/sat-competition-2017/benchmarks/Main.zip)
  : with a 2000 sec timeout, splr-0.1.0 solved:
  - 72 satisfiable problems: all the solutions were correct.
  - 51 unsatisfiable problems: [Lingeling](http://fmv.jku.at/lingeling/) or Glucose completely returns the same result. And,
    - 37 certificates generated by splr-0.1.1 were verified with drat-trim.
    - The remaining 14 certificates weren't able to be verified due to [timeout](https://gitlab.com/satisfiability01/splr/issues/74#note_142021555) by drat-trim.

## Technology Preview 13

- all clauses are stored into a single ClauseDB
- In-processing eliminator
- dynamic fitting of restart parameters

## Technology Preview 12

- `Solver` were divided into 6 sub modules
- resolved a performance regression
- switched to EVSIDS instead of ACID
- Glucose-style Watch structure
