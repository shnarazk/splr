## 0.4.0, 2020-12-31

- adapt to the output format defined in chapter 5 of [SAT competition 2011 rules](http://www.satcompetition.org/2011/rules.pdf)
- merge assign.rs and var.rs into a module
- better modularity and abstraction via traits
- add and refactor restart module: `GeometricStabilizer`, `ProgressLBD`
- change a lot of options' meanings and mnemonics
- add some features for development: boundary_check, EVSIDS, trace_analysis
- `propagate` skips up to the last position
- remove code about 'deep search' completely, superseded with stabilizing mode
- stop *too* dynamic var decay control
- change the activation timings of simplification
- stats data are stored in each module
- activate `JUST_USED` for clause reduction
- implement a simple re-phase mechanism
- implement `TryFrom<Vec<Vec<i32>>> for Certificate` for on-memory solving

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

## Technology Preview 13

- all clauses are stored into a single ClauseDB
- In-processing eliminator
- dynamic fitting of restart parameters

## Technology Preview 12

- `Solver` were divided into 6 sub modules
- resolved a performance regression
- switched to EVSIDS instead of ACID
- Glucose-style Watch structure
