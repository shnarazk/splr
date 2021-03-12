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

#### Version 0.6.0

_Warning: Version 0.6.0 isn't the best version._ It changed most modules like var reward mechanism, restart policy and in-processor timing.

- all the certifications of [UUF250](https://github.com/shnarazk/SAT-bench/tree/master/3-SAT/UUF250) were correct and verified with [Grad](https://www21.in.tum.de/~lammich/grat/).
- [SAT Race 2019](http://sat-race-2019.ciirc.cvut.cz), [Benchmarks](http://satcompetition.org/sr2019benchmarks.zip) -- splr-0.6.0 RC() solved with a 300 sec (soft) timeout:
  - 45 (20201226), 42 (eab832c), and 38 (0.6.0) satisfiable problems: all the solutions were correct.
  - 6 (20201226), 4 (eab832c), and 4 (0.6.0) unsatisfiable problems: all the certifications were verified with [Grad](https://www21.in.tum.de/~lammich/grat/).

![Benchmark result(2021-01-16)](https://user-images.githubusercontent.com/997855/104808677-24d97080-582b-11eb-85af-d01fd161bafd.png)

## Install

Just run `cargo install splr` after installing the latest [cargo](https://www.rust-lang.org/tools/install).
Two executables will be installed:

- `splr` -- the solver
- `dmcr` -- a very simple model checker to verify a *satisfiable* assignment set which was generated by `splr`.

## Usage

Splr is a standalone program, taking a CNF file. The result will be saved to a file, which format is
defined by [SAT competition 2011 rules](http://www.satcompetition.org/2011/rules.pdf).

```plain
$ splr tests/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
unif-k3-r4.25-v360-c1530-S1293537826-039.cnf       360,1530 |time:   309.35
 #conflict:    4156094, #decision:      5251386, #propagate:      225262345
  Assignment|#rem:      350, #ass:        1, #elm:        9, prg%:   2.7778
      Clause|Remv:    89387, LBD2:     1163, Binc:       28, Perm:     1538
     Restart|#BLK:        0, #RST:    30968, trgr:        1, peak:      128
         LBD|avrg:  10.5611, trnd:   0.9841, depG:   2.9608, /dpc:     1.36
    Conflict|tASG:   0.9761, cLvl:    12.85, bLvl:    11.68, /ppc:    50.32
        misc|elim:        7, #sub:        0, core:        0, /cpr:   123.60
      Result|file: ./.ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
s SATISFIABLE: tests/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```

```plain
$ cat .ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c This file was generated by splr-0.7.0 for ../SAT-bench/SAT09/RANDOM/MEDIUM/3SAT/SATISFIABLE/360/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c
c CNF file(unif-k3-r4.25-v360-c1530-S1293537826-039.cnf), #var:      360, #cls:     1530
c  #conflict:    4156094, #decision:      5251386, #propagate:      225262345,
c   Assignment|#rem:      350, #fix:        1, #elm:        9, prg%:   2.7778,
c       Clause|Remv:    89387, LBD2:     1163, Binc:       28, Perm:     1538,
c      Restart|#BLK:        0, #RST:    30968, trgr:        1, peak:      128,
c          LBD|avrg:  10.5611, trnd:   0.9841, depG:   2.9608, /dpc:     1.36,
c     Conflict|tASG:   0.9761, cLvl:    12.85, bLvl:    11.68, /ppc:    50.32,
c         misc|elim:        7, #sub:        0, core:        0, /cpr:   123.60,
c     Strategy|mode:  generic, time:   309.35,
c
s SATISFIABLE
v 1 -2 3 4 5 6 -7 -8 9 -10 -11 -12 13 -14 -15 16 17 18 -19 20 ... -359 -360 0
```

```plain
$ dmcr tests/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
A valid assignment set for tests/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf is found in .ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```
If you want to certificate unsatisfiability, use `splr --certificate` and recommend to use [Grid](https://www21.in.tum.de/~lammich/grat/).

1. Run splr with certificate option.

```plain
$ splr -c tests/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
unif-k3-r4.25-v360-c1530-S1028159446-096.cnf       360,1530 |time:    77.92
 #conflict:    1531986, #decision:      1922419, #propagate:       80871699
  Assignment|#rem:      279, #ass:       73, #elm:        8, prg%:  22.5000
      Clause|Remv:   120822, LBD2:      752, Binc:      185, Perm:     1657
     Restart|#BLK:        0, #RST:    12160, trgr:        1, peak:        1
         LBD|avrg:   4.0368, trnd:   0.5933, depG:   1.9282, /dpc:     1.14
    Conflict|tASG:   0.9954, cLvl:     7.47, bLvl:     6.34, /ppc:    53.05
        misc|elim:        4, #sub:       23, core:      171, /cpr:   160.59
      Result|file: ./.ans_unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
 Certificate|file: proof.out
s UNSATISFIABLE: tests/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
```

2. Trim comments from the output

```plain
$ egrep -v '^[cs]' < proof.out > proof.drat
```

3. Convert the drat file to a grat file.

```plain
$ gratgen tests/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf proof.drat -o proof.grat
c sizeof(cdb_t) = 4
c sizeof(cdb_t*) = 8
c Using RAT run heuristics
c Parsing formula ... 1ms
c Parsing proof (ASCII format) ... 12075ms
c Forward pass ... 2763ms
c Starting Backward pass
c Single threaded mode
c Waiting for aux-threads ...done
c Lemmas processed by threads: 1381423 mdev: 0
c Finished Backward pass: 50489ms
c Writing combined proof ... 14515ms
s VERIFIED
c Timing statistics (ms)
c Parsing:  12077
c Checking: 53273
c   * bwd:  50489
c Writing:  14515
c Overall:  79878
c   * vrf:  65363

c Lemma statistics
c RUP lemmas:  1381423
c RAT lemmas:  0
c   RAT run heuristics:   0
c Total lemmas:  1381423

c Size statistics (bytes)
c Number of clauses: 1535302
c Clause DB size:  105203416
c Item list:       47143024
c Pivots store:    8388608
```

4. Verify it with `gratchk`

```plain
$ gratchk unsat tests/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf proof.grat
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
| `depG'       | the EMA of LBD of the clauses used in conflict analysis                                   |
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
      --rat <rst-asg-thr>   Blocking restart threshold              0.20
      --rll <rst-lbd-len>   Length of LBD fast EMA                 24
      --rls <rst-lbd-slw>   Length of LBD slow EMA               8192
      --rlt <rst-lbd-thr>   Forcing restart threshold               1.20
      --rs  <rst-step>      #conflicts between restarts            24
      --srd <stg-rwd-dcy>   Decay rate for staged var reward        0.50
      --srv <stg-rwd-val>   Extra reward for staged vars            1.00
      --vdr <vrw-dcy-rat>   Var reward decay rate                   0.94
      --vds <vrw-dcy-stp>   Var reward decay change step            0.10
ARGS:
  <cnf-file>    DIMACS CNF file
```

## License

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at http://mozilla.org/MPL/2.0/.

---

2020-2021, Narazaki Shuji
