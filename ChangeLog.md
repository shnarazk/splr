## 0.1.2, 2019-03-07

- tweak heuristic adaptation, restart, and clause/variable elimination modules
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
- switched to VSIDS instead of ACID
- Glucose-style Watch structure
