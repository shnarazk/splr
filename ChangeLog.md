## 0.1.1

- 'splr --certify' generates DRAT, certificates of unsatisfiability.
- Clause id was changed from u64 to u32.
- The answer file format was slightly modified.

## 0.1.0, 2019-02-14

- Answers were verified with Glucose and Lingeling.

## Technology Preview 13

- all clauses are stored into a single ClauseDB
- In-processing eliminator
- dynamic fitting of restart parameters

## Technology Preview 12

- `Solver` were divided into 6 sub modules
- resolved a perfomance regression
- switched to VSIDS instead of ACID
- Glucose-style Watch structure
