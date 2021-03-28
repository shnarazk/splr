## A modern SAT Solver for Propositional Logic in Rust

Splr is a pure [Rust](https://www.rust-lang.org)ic modern SAT solver, based on [Glucose 4.1](https://www.labri.fr/perso/lsimon/glucose/).
It adopts various research results on SAT solvers:

- _CDCL_, _watch literals_, _LBD_ and so on from Glucose, [Minisat](http://minisat.se) and the ancestors
- Glucose-like _dynamic blocking/forcing restarts_ based on [EMAs](https://arxiv.org/abs/1506.08905)
- pre/in-process simplification based on clause subsumption and variable elimination
- compile-time selection of a variant of _Learning Rate Based Branching_ with _Reason Side Rewarding_ and EVSIDS
- _chronological backtrack_ aka _chronoBT_
- Glucose-like heuristics adaptation
- [CaDiCaL](https://github.com/arminbiere/cadical)-like extended phase saving
- a variant of CaDiCaL-like search stabilization
- _clause vivification_ by {pre,in}-processor

*Many thanks to SAT researchers.*

Please check [ChangeLog](ChangeLog.md) about recent updates.

## Correctness

Though Splr comes with **ABSOLUTELY NO WARRANTY**, I'd like to show some results.

#### Version 0.7.1

_Warning: Version 0.7.1 is not the best but a pretty good version._

- all the certifications of [UUF250](https://github.com/shnarazk/SAT-bench/tree/master/3-SAT/UUF250) were correct and verified with [Grad](https://www21.in.tum.de/~lammich/grat/).
- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip) -- splr-0.7.1 RC(a73ab46c) solved with a 400 sec timeout:
  - 47 satisfiable problems: all the solutions were correct.
  - 12 unsatisfiable problems: all the certifications were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![Benchmark result(2021-01-16)](https://user-images.githubusercontent.com/997855/104808677-24d97080-582b-11eb-85af-d01fd161bafd.png)

## Install

Just run `cargo install splr` after installing the latest [cargo](https://www.rust-lang.org/tools/install).
Two executables will be installed:

- `splr` -- the solver
- `dmcr` -- a very simple model checker to verify a *satisfiable* assignment set which was generated by `splr`.

Alternatively, Nix users can use `nix build`.

## Usage

Splr is a standalone program, taking a CNF file. The result will be saved to a file, which format is
defined by [SAT competition 2011 rules](http://www.satcompetition.org/2011/rules.pdf).

```plain
$ splr cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf 
unif-k3-r4.25-v360-c1530-S1293537826-039.cnf       360,1530 |time:    70.08
 #conflict:    1172695, #decision:      1652565, #propagate:       64414971
  Assignment|#rem:      351, #ass:        0, #elm:        9, prg%:   2.5000
      Clause|Remv:    48653, LBD2:      493, Binc:        0, Perm:    26566
     Restart|#BLK:        0, #RST:     8952, trgr:        1, peak:       64
         LBD|avrg:  13.4442, trnd:   1.1686, depG:   2.8988, /dpc:     1.42
    Conflict|tASG:   0.9624, cLvl:    14.51, bLvl:    13.36, /ppc:    63.24
        misc|elim:        2, #sub:        0, core:        0, /cpr:    76.72
      Result|file: ./ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
s SATISFIABLE: cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```

```plain
$ cat ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c This file was generated by splr-0.7.1 for cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c 
c unif-k3-r4.25-v360-c1530-S1293537826-039.cnf, #var:      360, #cls:     1530
c  #conflict:    1172695, #decision:      1652565, #propagate:       64414971,
c   Assignment|#rem:      351, #fix:        0, #elm:        9, prg%:   2.5000,
c       Clause|Remv:    48653, LBD2:      493, Binc:        0, Perm:    26566,
c      Restart|#BLK:        0, #RST:     8952, trgr:        1, peak:       64,
c          LBD|avrg:  13.4442, trnd:   1.1686, depG:   2.8988, /dpc:     1.42,
c     Conflict|tASG:   0.9624, cLvl:    14.51, bLvl:    13.36, /ppc:    63.24,
c         misc|elim:        2, #sub:        0, core:        0, /cpr:    76.72,
c     Strategy|mode:  generic, time:    70.09,
c   config::ChronoBtThreshold                      100
c   config::ClauseRewardDecayRate                 0.95
c   config::InprocessorInterval                  16384
c   config::RestartAsgThreshold                   0.75
c   config::RestartLbdThreshold                    1.1
c   config::VarRewardDecayRate                    0.94
c   assign::NumConflict                        1172695
c   assign::NumDecision                        1652565
c   assign::NumPropagation                    64414971
c   assign::NumRephase                               3
c   assign::NumRestart                            8953
c   assign::NumVar                                 360
c   assign::NumAssertedVar                           0
c   assign::NumEliminatedVar                         9
c   assign::NumUnassertedVar                       351
c   assign::NumUnassignedVar                       351
c   assign::NumUnreachableVar                        0
c   assign::DecisionPerConflict                      1.417
c   assign::PropagationPerConflict                  63.243
c   assign::ConflictPerRestart                      76.026
c   clause::NumBiClause                              0
c   clause::NumBiLearnt                              0
c   clause::NumClause                            75219
c   clause::NumLBD2                                493
c   clause::NumLearnt                            48653
c   clause::NumReduction                            48
c   clause::DpAverageLBD                             2.899
c   processor::NumFullElimination                    2
c   processor::NumSatElimination                     4
c   processor::NumSubsumedClause                     0
c   restart::NumBlock                                0
c   restart::NumCycle                                6
c   restart::NumRestart                           8953
c   restart::NumStage                              184
c   restart::TriggerLevel                            1
c   restart::TriggerLevelMax                        64
c   state::NoDecisionConflict                   586376
c   state::Vivification                             47
c   state::VivifiedClause                            0
c   state::VivifiedVar                               0
c   state::BackjumpLevel                            13.359
c   state::ConflictLevel                            14.515
c 
s SATISFIABLE
v 1 -2 3 4 5 6 -7 -8 9 -10 -11 -12 13 -14 ...  -360 0
```

```plain
$ dmcr cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
A valid assignment set for cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf is found in ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```
If you want to certificate unsatisfiability, use `splr --certificate` and recommend to use [Grid](https://www21.in.tum.de/~lammich/grat/).

1. Run splr with certificate option.

```plain
$ splr -c cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
unif-k3-r4.25-v360-c1530-S1028159446-096.cnf       360,1530 |time:   124.06
 #conflict:    1720154, #decision:      2342261, #propagate:       89154644
  Assignment|#rem:      268, #ass:       83, #elm:        9, prg%:  25.5556
      Clause|Remv:    25085, LBD2:     1327, Binc:      149, Perm:    28886
     Restart|#BLK:        0, #RST:    13786, trgr:        2, peak:       64
         LBD|avrg:   3.3013, trnd:   0.4555, depG:   1.9332, /dpc:     1.21
    Conflict|tASG:   0.9853, cLvl:     8.03, bLvl:     6.88, /ppc:    50.73
        misc|elim:        5, #sub:       72, core:      351, /cpr:   141.70
      Result|file: ./ans_unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
 Certificate|file: proof.out
s UNSATISFIABLE: cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
```

2. Trim comments from the output

```plain
$ egrep -v '^[cs]' < proof.out > proof.drat
```

3. Convert the drat file to a grat file.

```plain
$ gratgen cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf proof.drat -o proof.grat
c sizeof(cdb_t) = 4
c sizeof(cdb_t*) = 8
c Using RAT run heuristics
c Parsing formula ... 1ms
c Parsing proof (ASCII format) ... 14107ms
c Forward pass ... 3355ms
c Starting Backward pass
c Single threaded mode
c Waiting for aux-threads ...done
c Lemmas processed by threads: 1527555 mdev: 0
c Finished Backward pass: 74366ms
c Writing combined proof ... 15788ms
s VERIFIED
c Timing statistics (ms)
c Parsing:  14108
c Checking: 77745
c   * bwd:  74366
c Writing:  15788
c Overall:  107647
c   * vrf:  91859

c Lemma statistics
c RUP lemmas:  1527555
c RAT lemmas:  0
c   RAT run heuristics:   0
c Total lemmas:  1527555

c Size statistics (bytes)
c Number of clauses: 1720039
c Clause DB size:  121214776
c Item list:       54569664
c Pivots store:    8388608
```

4. Verify it with `gratchk`

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
| `#ass`       | the number of asserted variables (which has been assigned a value at decision level zero) |
| `#elm`       | the number of eliminated variables                                                        |
| `prg%`       | the percentage of `remaining variables / total variables`                                 |
| `Remv`       | the number of learnt clauses which are not biclauses                                      |
| `LBD2`       | the number of learnt clauses which LBDs are 2                                             |
| `Binc`       | the number of binary learnt clauses                                                       |
| `Perm`       | the number of given clauses and binary learnt clauses                                     |
| `#BLK`       | the number of blocking restart                                                            |
| `#RST`       | the number of restart                                                                     |
| `trgr`       | the number of the restart trigger before executing restart                                |
| `peak`       | the largest trigger so far                                                                |
| `avrg`       | the EMA, Exponential Moving Average, of LBD of learnt clauses                             |
| `depG`       | the EMA of LBD of the clauses used in conflict analysis                                   |
| `/dpc`       | the EMA of decisions per conflict                                                         |
| `tASG`       | the current trend of the number of assigned vars after restart                            |
| `cLvl`       | the EMA of decision levels at which conflicts occur                                       |
| `bLvl`       | the EMA of decision levels to which backjumps go                                          |
| `/ppc`       | the EMA of propagations per conflict                                                      |
| `elim`       | the number of invocations of clause/var elimination                                       |
| `#sub`       | the number of the clauses subsumed by caluse elimination processor                        |
| `core`       | the number of unreachable vars                                                            |
| `/cpr`       | the EMA of conflicts per restart                                                          |
| `mode`       | Selected strategy's id                                                                    |
| `time`       | the elapsed CPU time in seconds                                                           |

## Command line options

```plain
$ splr --help
A modern CDCL SAT solver in Rust
Activated features: clause elimination, clause reduction, Learning-Rate based rewarding, Luby stabilization, reason side rewarding

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
      --ii <c-ip-int>       #cls to start in-processor          16384
  -t, --timeout <timeout>   CPU time limit in sec.               5000
      --ecl <elm-cls-lim>   Max #lit for clause subsume            18
      --evl <elm-grw-lim>   Grow limit of #cls in var elim.         0
      --evo <elm-var-occ>   Max #cls for var elimination        20000
  -o, --dir <io-outdir>     Output directory                         .
  -p, --proof <io-pfile>    DRAT Cert. filename                 proof.out
  -r, --result <io-rfile>   Result filename/stdout                       
      --ral <rst-asg-len>   Length of assign. fast EMA             24
      --ras <rst-asg-slw>   Length of assign. slow EMA           8192
      --rat <rst-asg-thr>   Blocking restart threshold              0.75
      --rll <rst-lbd-len>   Length of LBD fast EMA                 24
      --rls <rst-lbd-slw>   Length of LBD slow EMA               8192
      --rlt <rst-lbd-thr>   Forcing restart threshold               1.10
      --rs  <rst-step>      #conflicts between restarts            24
      --srd <stg-rwd-dcy>   Decay rate for staged var reward        0.50
      --srv <stg-rwd-val>   Extra reward for staged vars            1.00
      --vdr <vrw-dcy-rat>   Var reward decay rate                   0.94
      --vds <vrw-dcy-stp>   Var reward decay change step            0.10
ARGS:
  <cnf-file>    DIMACS CNF file
```

## Solver description

Splr-0.7.1 adopts the following feature by default:

  - Learning-rate based var rewarding and clause rewarding
  - Reason-side var rewarding
  - dynamic restart blocking based on the number of remaining vars
  - dynamic restart based on average LBDs of learnt clauses
  - clause elimination and subsumption as pre-processor and in-processor
  - stabilization based on Luby series, or LubyStabilization
  - chronological backtrack and non-chronological backtrack
  - clause vivification
  - re-phase the best phases

Among them, the unique feature is LubyStabilization. Let me explain it.

To make special periods with very low restart rate, known as 'stabilization mode,' Splr changes
the number of restart trigger to execute restart.
Usually SAT solvers execute 'restart' when the average LBD of learnt clauses getting higher.
Splr requires that the condition holds by *N* times, where N is a value in the Luby series, and is changed during problem-solving. 
And, to avoid rapid parameters changes, Splr also introduces *stages* that share the same N. The length of stage is also controlled by Luby series.
Here are the relations of values.

- 'cycle' is a segment of stages, which is separated by highest Luby values.
- trigger_level *N* of stage *n* = Luby(*n*)
- length_of_stage *n* = (2 * max(Luby[*1*, *n*]) ) / *n*

|stage *n*|*N* = Luby(*n*)|cycle|max *N*|stage len|restart cond.| restart |
|--------:|--------------:|----:|------:|--------:|------------:|:-------:|
|      1  |             1 |   0 |     1 |       1 |           1 |       1 |
|      2  |             1 |   1 |     1 |       2 |           2 |       2 |
|      3  |         **2** |   1 |     1 |       1 |         3-4 |     3-4 |
|      4  |             1 |   2 |     2 |       4 |         5-6 |     5-8 |
|      5  |             1 |   2 |     2 |       4 |         7-8 |    9-12 |
|      6  |             2 |   2 |     2 |       2 |        9-10 |   13-14 |
|      7  |         **4** |   2 |     2 |       1 |       11-14 |      15 |
|      8  |             1 |   3 |     4 |       8 |       15-18 |   16-23 |
|      9  |             1 |   3 |     4 |       8 |       19-22 |   24-31 |
|      10 |             2 |   3 |     4 |       4 |       23-26 |   32-35 |
|      11 |             1 |   3 |     4 |       8 |       27-30 |   36-43 |
|      12 |             1 |   3 |     4 |       8 |       31-34 |   44-51 |
|      13 |             2 |   3 |     4 |       4 |       35-38 |   52-55 |
|      14 |             4 |   3 |     4 |       2 |       39-42 |   56-57 |
|      15 |         **8** |   3 |     4 |       1 |       43-50 |      58 |
|      16 |             1 |   4 |     8 |      16 |       51-58 |   59-74 |
|      17 |             1 |   4 |     8 |      16 |       59-66 |   75-90 |
|      18 |             2 |   4 |     8 |       8 |       67-74 |   91-98 |
|      19 |             1 |   4 |     8 |      16 |       75-82 |  99-114 |
|      20 |             1 |   4 |     8 |      16 |       83-90 | 115-130 |

You can see effects of LubyStabilization with the value of `trgr` for *N*, `peak` for max *N* and `/cpr` for 'conflict per restart'. Here's an example.

![](https://user-images.githubusercontent.com/997855/111037372-0c6e8680-8467-11eb-9512-5deecfa45885.png)

## License

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at http://mozilla.org/MPL/2.0/.

---

2020-2021, Narazaki Shuji
