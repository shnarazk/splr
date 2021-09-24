## A modern SAT Solver for Propositional Logic in Rust

Splr is a modern SAT solver in [Rust](https://www.rust-lang.org), based on [Glucose 4.1](https://www.labri.fr/perso/lsimon/glucose/).
It adopts various research results on modern SAT solvers:

- _CDCL_, _watch literals_, _LBD_ and so on from Glucose, [Minisat](http://minisat.se) and the ancestors
- Glucose-like _dynamic blocking/forcing restarts_
- pre/in-processor to simplify CNF
- branching variable selection based on _Learning Rate Based Branching_ with _Reason Side Rewarding_ or EVSIDS
- _chronological backtrack_
- [CaDiCaL](https://github.com/arminbiere/cadical)-like extended phase saving
- _restart stabilization_ inspired by CadiCaL
- _clause vivification_

*Many thanks to SAT researchers.*

Please check [ChangeLog](ChangeLog.md) about recent updates.

## Correctness

Though Splr comes with **ABSOLUTELY NO WARRANTY**, I'd like to show some results.

#### Version 0.12.0

- [SAT Competition 2021](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks main truck](http://satcompetition.org/sr2019benchmarks.zip) -- splr-0.12.0 RC (ed953b78) solved with a 500 sec timeout:
  - 42 satisfiable problems: all the solutions were correct.
  - 42 unsatisfiable problems: all the certifications were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

#### Version 0.11.0

- all the certifications of [UUF250](https://github.com/shnarazk/SAT-bench/tree/master/3-SAT/UUF250) were correct and verified with [Grad](https://www21.in.tum.de/~lammich/grat/).
- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip) -- splr-0.11.0 RC (84895b21) solved with a 300 sec timeout:
  - 43 satisfiable problems: all the solutions were correct.
  - 7 unsatisfiable problems: all the certifications were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![Benchmark result(2021-08-16)](https://user-images.githubusercontent.com/997855/129486985-4d76d819-98b7-4f4c-b532-c13dc672282d.png)

## Install

Just run `cargo install splr` after installing the latest [cargo](https://www.rust-lang.org/tools/install).
Two executables will be installed:

- `splr` -- the solver
- `dmcr` -- a very simple model checker to verify a *satisfiable* assignment set generated by `splr`.

Alternatively, Nix users can use `nix build`.

## Usage

Splr is a standalone program, taking a CNF file. The result will be saved to a file, which format is
defined by [SAT competition 2011 rules](http://www.satcompetition.org/2011/rules.pdf).

```plain
unif-k3-r4.25-v360-c1530-S1293537826-039.cnf       360,1530 |time:   721.28
 #conflict:    3527930, #decision:      6730814, #propagate:      186925863
  Assignment|#rem:      351, #fix:        0, #elm:        9, prg%:   2.5000
      Clause|Remv:    69093, LBD2:      773, BinC:        0, Perm:     1521
     Restart|#BLK:        0, #RST:    14222, *scl:        1, sclM:       32
         LBD|trnd:   0.8328, avrg:  10.2688, depG:   3.0410, /dpc:     1.19
    Conflict|tASG:   0.9836, cLvl:    15.21, bLvl:    14.07, /ppc:    57.09
        misc|vivC:     1351, subC:        0, core:      138, /cpr:   991.44
      Result|file: ./ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
s SATISFIABLE: cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```

```plain
$ cat ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c This file was generated by splr-0.11.0 for cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c 
c unif-k3-r4.25-v360-c1530-S1293537826-039.cnf, #var:      360, #cls:     1530
c  #conflict:    3527930, #decision:      6730814, #propagate:      186925863,
c   Assignment|#rem:      351, #fix:        0, #elm:        9, prg%:   2.5000,
c       Clause|Remv:    69093, LBD2:      773, BinC:        0, Perm:     1521,
c      Restart|#BLK:        0, #RST:    14222, *scl:        1, sclM:       32,
c          LBD|avrg:  10.2688, trnd:   0.8328, depG:   3.0410, /dpc:     1.19,
c     Conflict|tASG:   0.9836, cLvl:    15.21, bLvl:    14.07, /ppc:    57.09,
c         misc|vivC:      104, subC:        0, core:      138, /cpr:   991.44,
c     Strategy|mode:  generic, time:   721.29,
c 
c   config::ChronoBtThreshold                      100
c   config::ClauseRewardDecayRate                 0.95
c   config::InprocessorInterval                  10000
c   config::RestartAsgThreshold                    0.6
c   config::RestartLbdThreshold                    1.6
c   config::VarRewardDecayRate                    0.96
c   assign::NumConflict                        3527930
c   assign::NumDecision                        6730814
c   assign::NumPropagation                   186925863
c   assign::NumRephase                              60
c   assign::NumRestart                           14223
c   assign::NumVar                                 360
c   assign::NumAssertedVar                           0
c   assign::NumEliminatedVar                         9
c   assign::NumUnassertedVar                       351
c   assign::NumUnassignedVar                       351
c   assign::NumUnreachableVar                        0
c   assign::RootLevel                                0
c   assign::DecisionPerConflict                      1.190
c   assign::PropagationPerConflict                  57.089
c   assign::ConflictPerRestart                    1021.985
c   assign::ConflictPerBaseRestart                1021.985
c   assign::BestPhaseDivergenceRate                  0.263
c   clause::NumBiClause                              0
c   clause::NumBiClauseCompletion                    0
c   clause::NumBiLearnt                              0
c   clause::NumClause                            70614
c   clause::NumLBD2                                773
c   clause::NumLearnt                            69093
c   clause::NumReduction                           102
c   clause::NumReRegistration                        0
c   clause::Timestamp                          3527930
c   clause::DpAverageLBD                             3.041
c   processor::NumFullElimination                  104
c   processor::NumSubsumedClause                     0
c   restart::NumBlock                                0
c   restart::NumCycle                                5
c   restart::NumRestart                          14223
c   restart::NumStage                              102
c   restart::IntervalScale                           1
c   restart::IntervalScaleMax                       32
c   state::NumDecisionConflict                 1771382
c   state::NumProcessor                            103
c   state::Vivification                            103
c   state::VivifiedClause                         1351
c   state::VivifiedVar                               0
c   state::BackjumpLevel                            14.071
c   state::ConflictLevel                            15.207
c 
s SATISFIABLE
v 1 -2 3 4 5 6 -7 -8 9 -10 -11 -12 13 -14 ...  -360 0
```

```plain
$ dmcr cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
A valid assignment set for cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf is found in ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```

If you want to certificate unsatisfiability, use `--certify` or `-c` and use proof checker like [Grid](https://www21.in.tum.de/~lammich/grat/).

1. Run splr with the certificate option.

```plain
$ splr -c cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
unif-k3-r4.25-v360-c1530-S1028159446-096.cnf       360,1530 |time:   354.12
 #conflict:    2183312, #decision:      3933643, #propagate:      112056337
  Assignment|#rem:      350, #fix:        2, #elm:        8, prg%:   2.7778
      Clause|Remv:    68795, LBD2:      761, BinC:      532, Perm:     2013
     Restart|#BLK:        0, #RST:    13680, *scl:        2, sclM:       32
         LBD|trnd:   0.3261, avrg:   2.2739, depG:   2.1646, /dpc:     1.06
    Conflict|tASG:   1.0175, cLvl:     7.98, bLvl:     6.84, /ppc:    51.88
        misc|vivC:     1195, subC:        0, core:      350, /cpr:   201.37
      Result|file: ./ans_unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
 Certificate|file: proof.drat
s UNSATISFIABLE: cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
```

2. Convert the generated DRAT file to a GRAT file.

```plain
$ gratgen cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf proof.drat -o proof.grat
c sizeof(cdb_t) = 4
c sizeof(cdb_t*) = 8
c Using RAT run heuristics
c Parsing formula ... 2ms
c Parsing proof (ASCII format) ... 19986ms
c Forward pass ... 4417ms
c Starting Backward pass
c Single threaded mode
c Waiting for aux-threads ...done
c Lemmas processed by threads: 1936846 mdev: 0
c Finished Backward pass: 99600ms
c Writing combined proof ... 19980ms
s VERIFIED
c Timing statistics (ms)
c Parsing:  19989
c Checking: 104047
c   * bwd:  99600
c Writing:  19980
c Overall:  144024
c   * vrf:  124044

c Lemma statistics
c RUP lemmas:  1936846
c RAT lemmas:  0
c   RAT run heuristics:   0
c Total lemmas:  1936846

c Size statistics (bytes)
c Number of clauses: 2195700
c Clause DB size:  162762960
c Item list:       69104688
c Pivots store:    16777216
```

3. Verify it with `gratchk`.

```plain
$ gratchk unsat cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf proof.grat
c Reading cnf
c Reading proof
c Done
c Verifying unsat
s VERIFIED UNSAT
```

### Calling Splr from Rust programs

Since 0.4.0, you can use Splr in your programs.

```rust
use splr::*;
use std::convert::TryFrom;

fn main() {
    let v: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]];
    match Certificate::try_from(v) {
        Ok(Certificate::SAT(ans)) => println!("s SATISFIABLE: {:?}", ans),
        Ok(Certificate::UNSAT) => println!("s UNSATISFIABLE"),
        Err(e) => panic!("s UNKNOWN; {}", e),
    }
}
```

### All solutions SAT solver

```rust
use splr::*;
use std::{convert::TryFrom, env::args};

fn main() {
    let cnf = args().nth(1).expect("takes an arg");
    let assigns: Vec<i32> = Vec::new();
    println!("#solutions: {}", run(&cnf, &assigns));
}

#[cfg(feature = "incremental_solver")]
fn run(cnf: &str, assigns: &[i32]) -> usize {
    let mut solver = Solver::try_from(cnf).expect("panic at loading a CNF");
    for n in assigns.iter() {
        solver.add_assignment(*n).expect("panic at assertion");
    }
    let mut count = 0;
    loop {
        match solver.solve() {
            Ok(Certificate::SAT(ans)) => {
                count += 1;
                println!("s SATISFIABLE({}): {:?}", count, ans);
                let ans = ans.iter().map(|i| -i).collect::<Vec<i32>>();
                match solver.add_clause(ans) {
                    Err(SolverError::Inconsistent) => {
                        println!("c no answer due to level zero conflict");
                        break;
                    }
                    Err(e) => {
                        println!("s UNKNOWN; {:?}", e);
                        break;
                    }
                    Ok(_) => solver.reset(),
                }
            }
            Ok(Certificate::UNSAT) => {
                println!("s UNSATISFIABLE");
                break;
            }
            Err(e) => {
                println!("s UNKNOWN; {}", e);
                break;
            }
        }
    }
    count
}
```

Since 0.4.1, `Solver` has `iter()`. So you can iterate on satisfiable '`solution: Vec<i32>`'s as:

```rust
#[cfg(feature = "incremental_solver")]
for (i, v) in Solver::try_from(cnf).expect("panic").iter().enumerate() {
    println!("{}-th answer: {:?}", i, v);
}
```

### Mnemonics used in the progress message

| mnemonic     | meaning                                                                                   |
| ------------ | ----------------------------------------------------------------------------------------- |
| `#var`       | the number of variables used in the given CNF file                                        |
| `#cls`       | the number of clauses used in the given CNF file                                          |
| `time`       | elapsed CPU time in seconds (or wall-clock time if CPU time is not available)             |
| `#conflict`  | the number of conflicts                                                                   |
| `#decision`  | the number of decisions                                                                   |
| `#propagate` | the number of propagates (its unit is literal)                                            |
| `#rem`       | the number of remaining variables                                                         |
| `#fix`       | the number of asserted variables (which has been assigned a value at decision level zero) |
| `#elm`       | the number of eliminated variables                                                        |
| `prg%`       | the percentage of `remaining variables / total variables`                                 |
| `Remv`       | the current number of learnt clauses that are not bi-clauses                              |
| `LBD2`       | the accumulated number of learnt clauses which LBDs are 2                                 |
| `BinC`       | the current number of binary learnt clauses                                               |
| `Perm`       | the current number of given clauses and binary learnt clauses                             |
| `#BLK`       | the number of blocking restarts                                                           |
| `#RST`       | the number of restarts                                                                    |
| `*scl`       | the scaling factor for restart interval used in Luby stabilization                        |
| `sclM`       | the largest scaling factor so far                                                         |
| `avrg`       | the EMA, Exponential Moving Average, of LBD of learnt clauses                             |
| `trnd`       | the current trend of the LBD's EMA                                                        |
| `depG`       | the EMA of LBD of the clauses used in conflict analysis                                   |
| `/dpc`       | the EMA of decisions per conflict                                                         |
| `tASG`       | the current trend of the number of assigned vars after restart                            |
| `cLvl`       | the EMA of decision levels at which conflicts occur                                       |
| `bLvl`       | the EMA of decision levels to which backjumps go                                          |
| `/ppc`       | the EMA of propagations per conflict                                                      |
| `vivC`       | the number of the vivified clauses                                                        |
| `subC`       | the number of the clauses subsumed by clause elimination processor                        |
| `core`       | the number of unreachable vars                                                            |
| `/cpr`       | the EMA of conflicts per restart                                                          |
| `mode`       | Selected strategy's id                                                                    |
| `time`       | the elapsed CPU time in seconds                                                           |

## Command line options

```plain
$ splr --help
A modern CDCL SAT solver in Rust
Activated features: best phase tracking, binary clause completion, clause elimination, clause vivification, Learning-Rate based rewarding, Luby stabilization, reason side rewarding, stage-based rephase

USAGE:
  splr [FLAGS] [OPTIONS] <cnf-file>
FLAGS:
  -h, --help                Prints help information
  -C, --no-color            Disable coloring
  -q, --quiet               Disable any progress message
  -c, --certify             Writes a DRAT UNSAT certification file
  -j, --journal             Shows sub-module logs
  -l, --log                 Uses Glucose-like progress report
  -V, --version             Prints version information
OPTIONS (red options depend on features in Cargo.toml):
      --cbt <c-cbt-thr>     Dec. lvl to use chronoBT              100
      --cdr <crw-dcy-rat>   Clause reward decay rate                0.95
      --cl <c-cls-lim>      Soft limit of #clauses (6MC/GB)         0
      --ii <c-ip-int>       #cls to start in-processor          10000
  -t, --timeout <timeout>   CPU time limit in sec.               5000
      --ecl <elm-cls-lim>   Max #lit for clause subsume            18
      --evl <elm-grw-lim>   Grow limit of #cls in var elim.         0
      --evo <elm-var-occ>   Max #cls for var elimination        20000
  -o, --dir <io-outdir>     Output directory                         .
  -p, --proof <io-pfile>    DRAT Cert. filename                 proof.drat
  -r, --result <io-rfile>   Result filename/stdout                       
      --ral <rst-asg-len>   Length of assign. fast EMA             24
      --ras <rst-asg-slw>   Length of assign. slow EMA           8192
      --rat <rst-asg-thr>   Blocking restart threshold              0.60
      --rll <rst-lbd-len>   Length of LBD fast EMA                  8
      --rls <rst-lbd-slw>   Length of LBD slow EMA               8192
      --rlt <rst-lbd-thr>   Forcing restart threshold               1.60
      --rs  <rst-step>      #conflicts between restarts             2
      --srd <stg-rwd-dcy>   Decay rate for staged var reward        0.50
      --srv <stg-rwd-val>   Extra reward for staged vars            1.00
      --vdr <vrw-dcy-rat>   Var reward decay rate                   0.94
      --vds <vrw-dcy-stp>   Var reward decay change step            0.10
ARGS:
  <cnf-file>    DIMACS CNF file
```

## Solver description

Splr-0.11.0 adopts the following features by default:

- Learning-rate based var rewarding and clause rewarding[3]
- Reason-side var rewarding[3]
- chronological backtrack and non-chronological backtrack[4]
- clause vivification[5]
- dynamic restart blocking based on the number of remaining vars[2]
- dynamic restart based on average LBDs of learnt clauses[1]
- clause elimination and subsumption as pre-processor and in-processor
- stabilization based on Luby series, or _Luby Stabilization_
- re-phase the best phases

As shown in the blow, Splr calls in-processor very frequently.

![search algorithm in Splr 0.11](https://user-images.githubusercontent.com/997855/129641237-f33ca231-711c-4f3c-9fdd-31dfd92aaa8a.png)


_Luby stabilization_ is an original mechanism to make long periods without restarts, which are called stabilized modes.
This method updates the restart interval, which usually has a constant value, as follows:

```
restart_interval = luby(n) * base_interval;
```
where `n` represents the number of updates, and `luby(n)` is a function returning _n_-th number of Luby series.
The longer the solver searches, the larger the average value is. So we can periodically explore the search space more deeply.
Here is an example.

![](https://user-images.githubusercontent.com/997855/128656027-a8eaa082-d2f8-4801-860e-46f38fa65c39.png)

Note: the mechanism explained here is different from that used in Splr-0.10.0.

#### Bibliography

- [1] G. Audemard and L. Simon, "Predicting learnt clauses quality in modern SAT solvers," in _International Joint Conference on Artificial Intelligence 2009_, pp. 399–404, 2009.

- [2] G. Audemard and L. Simon, "Refining restarts strategies for SAT and UNSAT," in _Lecture Notes in Computer Science_, vol.7513, pp.118–126, 2012.

- [3] J. H. Liang, V. Ganesh, P. Poupart, and K. Czarnecki, "Learning Rate Based Branching Heuristic for SAT Solvers," in _Lecture Notes in Computer Science_, vol.9710, pp.123–140, 2016.

- [4] A. Nadel and V. Ryvchin, "Chronological Backtracking," in _Theory and Applications of Satisfiability Testing - SAT 2018_, June 2018, pp.111–121, 2018.

- [5] C. Piette, Y. Hamadi, and L. Saïs, "Vivifying propositional clausal formulae," _Front. Artif. Intell. Appl._, vol.178, pp.525–529, 2008.

## License

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at http://mozilla.org/MPL/2.0/.

---

2020-2021, Narazaki Shuji
