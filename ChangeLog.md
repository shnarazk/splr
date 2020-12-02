## 0.6.0, 2020-12-01

- delete dependencies on 'libc' and 'structopt'
- make Splr *monotonous*, by removing timer based decision makers. Monotonous means that if a solver solves a problem within T timeout, it solves the problem within any timeout longer than T.
- Solver::restart provides both of `restart` and `stabilize`
- fix a bug in chronoBT, that occurred if a conflicting clause has just a single literal at the conflicting level.
- revise command line option parser to handle the last option better
- stabilization span is controlled with Luby sequence
- make stabilization modes affect var rewards
- make the learning rate of var rewarding an constant
- add two configuration options: explore_timestamp, moving_var_reward_rate

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

## 0.4.1, 2020-05-28

- the installation command is changed to `cargo install splr --features cli`
- add feature "incremental_solver" providing `SatSolverIF::{add_assign, add_var, reset}` and `Solver::iter` and delete some old features
- `cargo build --lib` doesn't depend on 'libc', 'structopt' and 'time' anymore; Splr can be compiled to WASM
- `--quiet` option stops progress report completely
- a tiny modification on var selection heuristics
- squash git history on the master branch

#### Verification

* [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip),  splr-0.4.1(be30d17, 7064c9) solved with a 400 sec (soft) timeout:
  * 48 satisfiable problems: all the solutions were correct.
  * 7 unsatisfiable problems: all were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

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

* [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip),  splr-0.4.0(e0461bd) solved with a 300 sec (soft) timeout:
  * 43 satisfiable problems: all the solutions were correct.
  * 4 unsatisfiable problems: all were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

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

* [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip),  splr-0.3.1 solved with a 200 sec (soft) timeout:
  * 35 satisfiable problems: all the solutions were correct.
  * 4 unsatisfiable problems:
    * 3 were verified with Grad.
    * Verifying gto_p60c238-sc2018.cnf was timed out due to the size of the drat file (1.3 GB).


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
- better tests in src/*.rs
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
- The literal endconding uses even integers for positive literals
- `Lbool` was changed to `Option<bool>`

## 0.1.4, 2019-09-12

- fix wrong computations about `State::{c_lvl, b_lvl}`, `Clause::activity`
- add '--stat' option to dump a history of internal state
- add new structs for better modulality: `ProgressEvaluator`, `RestartExecutor`, `VarDB`

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
* The first 100 problems from
  [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html),
  [250 variables uniform random satisfiable 3-SAT](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf250-1065.tar.gz)
  : all the solutions were correct.
* The first 100 problems from
  [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html),
  [250 variables uniform random unsatisfiable 3-SAT](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf250-1065.tar.gz)
  : all the solutions were correct and verified with [drat-trim](http://www.cs.utexas.edu/~marijn/drat-trim/).
* [SAT Competition 2017](https://baldur.iti.kit.edu/sat-competition-2017/index.php?cat=tracks),
  [Main track](https://baldur.iti.kit.edu/sat-competition-2017/benchmarks/Main.zip)
  : with a 2000 sec timeout, splr-0.1.0 solved:
  * 72 satisfiable problems: all the solutions were correct.
  * 51 unsatisfiable problems: [Lingeling](http://fmv.jku.at/lingeling/) or Glucose completely returns the same result. And,
     * 37 certificates generated by splr-0.1.1 were verified with drat-trim.
     * The remaining 14 certificates weren't able to be verified due to [timeout](https://gitlab.com/satisfiability01/splr/issues/74#note_142021555) by drat-trim.

## Technology Preview 13

- all clauses are stored into a single ClauseDB
- In-processing eliminator
- dynamic fitting of restart parameters

## Technology Preview 12

- `Solver` were divided into 6 sub modules
- resolved a performance regression
- switched to EVSIDS instead of ACID
- Glucose-style Watch structure
