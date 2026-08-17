## A modern SAT Solver for Propositional Logic in Rust

Splr is a modern and deterministic SAT solver in [Rust](https://www.rust-lang.org), inspired by [Glucose 4.1](https://www.labri.fr/perso/lsimon/glucose/) and [Kissat](https://github.com/arminbiere/kissat).
It adopts, or adopted, various research results on modern SAT solvers:

- _CDCL_, _watch literals_, _LBD_ and so on from Kissat, Glucose, [Minisat](http://minisat.se) and the ancestors
- Luby series based restart control. The current implementation of the Luby series has $O(1)$ time complexity and $O(1)$ space complexity.
  [Its correctness is proved in Lean4](https://github.com/shnarazk/LubySequence).
- pre/in-processor to simplify the given CNF
- two branching variable selection schemes: _Learning-Rate Based Branching_ (LRB) with _Reason Side Rewarding_ and _Variable Move To the Front_ (VMTF)
- _clause vivification_
- _trail saving_
- various rephasing schemes

*Many thanks to SAT researchers.*

Please check [ChangeLog](ChangeLog.md) about recent updates.

## Correctness

Though Splr comes with **ABSOLUTELY NO WARRANTY**, I'd like to show some results.

#### Version 0.19.0

- All satisfiable problems were checked by `dmcr` (src/bin/dmcr)
- All unsatisfiable problems were checked by `drat-trim`

| # | CNF picked from [SAT Competition 2025](https://satcompetition.github.io/2025/) |time (s)|ret|result|
|--:|:----------------------------------------------------|-------:|:-:|:--:|
|  1|`04648cef5bed430ab6429991fa9e107d-ramsey_3_6_19.norm`|   TO   |124| -- |
|  2|`0c0430a68f147be18ab3fded07f30fdb-oddball_53_5_tto_z`| 1159.27| 10| ✅ |
|  3|`0ccb0f855352783a972be45188bf3164-SCPC-500-12.cnf`   |   76.68| 20| ✅ |
|  4|`0e1d562093d5f4fc9013cf4a14a03f70-Break_12_50.xml.cn`|   12.19| 10| ✅ |
|  5|`110f8eb8b9b80204fe955ea0973bbb00-clqcl_30_7_6.norma`|   TO   |124| -- |
|  6|`24bde22f729a988fb2394b644cb60d39-SC25_Timetable_C_4`|   12.00| 10| ✅ |
|  7|`2d0c041c0fe72dc32527bfbf34f63e61-170223547.cnf`     |   TO   |124| -- |
|  8|`35b9091b90bd28a492c9556d6fc4348d-bp4_TCO_CSO_ZR.nor`|  606.28| 10| ✅ |
|  9|`35ec95b9b2398fb522db178855016ae0-MVRoundRobin_n14_d`|   TO   |124| -- |
| 10|`46a8727e27d848faafd83a990c2e01a7-case8.normalised.c`|   TO   |124| -- |
| 11|`482295be38dc1d63a16f3cf649ef7ef6-myciel6-cn.used-as`| 4296.87| 20| ✅ |
| 12|`53c21f3e78f060883026b5a12ba691d8-maximum_constraine`|   14.02| 10| ✅ |
| 13|`57b478982ee9aba245ba792452b18fe3-VanDerWaerden_pd_2`|  334.90| 10| ✅ |
| 14|`6147e666b75f603a4c4490d21ab654cd-hid-uns-enc-6-1-0-`|  790.16| 20| ✅ |
| 15|`65f7145996bbec02b90bd0fa64a20502-test_v7_r12_vr10_c`|   TO   |124| -- |
| 16|`68e33d998466bbdd4bfb7249a5790e4f-arles_thres10_p10_`|    0.02| 20| ✅ |
| 17|`83aa254f7d17e1df7bee19322ac4752b-1.normalised.cnf`  |   TO   |124| -- |
| 18|`8e62c5d47920ffe36052f86177403e70-SC25_Timetable_C_3`|   26.73| 10| ✅ |
| 19|`908433870bee8ba2c86f266d0b002fdb-MVRoundRobin_n20_d`|   TO   |124| -- |
| 20|`918d9e7c2e197312517736421d728958-SCPC-500-1.cnf`    |  118.29| 20| ✅ |
| 21|`91c429adc2dc8430461b6d87a9aef335-16_16_booth_wallac`|   TO   |124| -- |
| 22|`967b58fea99a99b8da592d3e2fe7139b-dubois50.cnf.mis-9`|   TO   |124| -- |
| 23|`98a9352230efc411c092f1dcdcdedcfc-bp4_BC012_IXA_LPI_`|   TO   |124| -- |
| 24|`9b5f767eb5c14eb888d51acf70e045c8-uniqinv40prop.cnf` | 2606.99| 20| ✅ |
| 25|`a0bcdaffb0ea36b678899fd86bdc7f18-arles_thres10_p10_`|    0.03| 20| ✅ |
| 26|`a1fdd60d2570f47fb14956ac9e96951f-oddball_22_5_ttf.n`|   29.45| 20| ✅ |
| 27|`a70883771fd1c210d94a916d52510a3a-gm28sparrc.cnf`    |   15.67| 20| ✅ |
| 28|`b3d3680b3287a989ce61a6db1054efd2-case20.normalised.`|   34.24| 10| ✅ |
| 29|`b9ed6fd14f4fc969ec966a4b54c36872-n320p5q2_n.apx_16.`|   67.38| 10| ✅ |
| 30|`c21096fa2f550785c33dc862d83bc941-case17.normalised.`|  441.79| 10| ✅ |
| 31|`cb950b9accfb53eb98f77b0f995ac0ae-rphp5_050_shuffled`|   TO   |124| -- |
| 32|`d5928883c1e1f70764a31a83aa419eaf-oski15a01b42s_opt.`|   TO   |124| -- |
| 33|`d8666a18cf3a32af0a606099f0070b4b-7.normalised.cnf`  |   TO   |124| -- |
| 34|`ddf9620410e6a4351f64c745670ef5d4-oddball_57_5_tto_z`| 1432.37| 10| ✅ |
| 35|`e23edb67db2d1dfdbfe2f4c02d09c6c7-14.normalised.cnf` | 1010.25| 10| ✅ |
| 36|`e430acf720b63044e5c825a00a76b0eb-rphp_p25_r25.cnf`  |   TO   |124| -- |
| 37|`e442248e155eb81a811edd1deca8a2cd-sudoku-N30-23.cnf` |   TO   |124| -- |
| 38|`f17dfbed8c18716a41b231702e127524-SC25_Timetable_C_4`|  667.20| 10| ✅ |
| 39|`f25a1df88f89c6bcbe2602fa7f6e816b-1-TC-256-K-63.sani`|  399.84| 10| ✅ |
| 40|`f33a6163305d6559043b7438a692dea9-simon-r17-1.saniti`| 2991.86| 10| ✅ |

med:    226.59, max:   4296.87,total (except 16 timeouts): 17144.50

#### Version 0.17.0

- [SAT Competition 2021](https://satcompetition.github.io/2021/), [Benchmarks main track](https://satcompetition.github.io/2021/benchmarks.html) -- splr-0.17.0 solved with a 300 sec timeout (this is one of the best of splr):
  - 49 satisfiable problems: all the solutions were correct.
  - 34 unsatisfiable problems: all certifications were verified with [Grat toolchain](https://www21.in.tum.de/~lammich/grat/) or [drat-trim](https://github.com/marijnheule/drat-trim).

## Install

Just run `cargo install splr` after installing the latest [cargo](https://www.rust-lang.org/tools/install).
Two executables will be installed:

- `splr` -- the solver
- `dmcr` -- a very simple model checker to verify a *satisfiable* assignment set generated by `splr`.

Alternatively, Nix users can use `nix build`.

### About `no_std` environment and feature `no_IO`

If you want to build a library for `no_std` environment,
or if you want to compile with feature `no_IO`,
you have to run `cargo build --lib --features no_IO`.
They are incompatible with `cargo install`.

- [2024-02-03] Feature `platform_wasm` was added.

## Usage

Splr is a standalone program, taking a CNF file. The result will be saved to a file, whose format is
defined by [SAT competition 2011 rules](http://www.satcompetition.org/2011/rules.pdf).

```plain
$ splr cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
unif-k3-r4.25-v360-c1530-S1293537826-039.cnf       360,1530 |time:  1653.99
 #conflict:    8496129, #decision:     13925320, #propagate:      398292916
  Assignment|#rem:      350, #fix:        0, #elm:       10, prg%:   2.7778
      Clause|Remv:    78724, LBD2:    53329, BinC:        0, Perm:     1522
    Conflict|cLvl:    17.39, bLvl:    16.25,  LBD:    16.52, /cpr: 39415.27
  Luby stage| idx:      263, ti1%:    19.00, ti2%:     0.41, /dpc:     1.27
      LRB(★)| LRB:    17.86, VMTF:    17.86, core:      128, /ppc:    56.77
      Result|file: ./ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
s SATISFIABLE: cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```

```plain
$ cat ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c This file was generated by splr-0.19.0 for cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
c
c unif-k3-r4.25-v360-c1530-S1293537826-039.cnf, #var:      360, #cls:     1530
c  #conflict:    8496129, #decision:     13925320, #propagate:      398292916,
c   Assignment|#rem:      350, #fix:        0, #elm:       10, prg%:   2.7778,
c       Clause|Remv:    78724, LBD2:    53329, BinC:        0, Perm:     1522,
c     Conflict|cLvl:  17.3942, bLvl:  16.2540, #RST:      350, /cpr: 39415.27,
c      Learing| LBD:  16.5243, ti1%:  18.9986, ti2%:     0.41, /dpc:     1.27,
c         misc| LRB:    17.86, VMTF:    17.86, core:      128, /ppc:    56.77,
c     Strategy|mode:  generic, time:  1653.99,
c
c   assign::NumConflict                        8496129
c   assign::NumDecision                       13925320
c   assign::NumPropagation                   398292916
c   assign::NumRestart                             264
c   assign::NumVar                                 360
c   assign::NumAssertedVar                           0
c   assign::NumEliminatedVar                        10
c   assign::NumReconflict                          704
c   assign::NumRepropagation                    417429
c   assign::NumUnassertedVar                       350
c   assign::NumUnassignedVar                       350
c   assign::RootLevel                                0
c   assign::DecisionPerConflict                      1.272
c   assign::PropagationPerConflict                  56.765
c   assign::ConflictPerRestart                   39031.375
c   assign::ConflictPerBaseRestart               39031.375
c   assign::ConlictDistanceAverage                   0.000
c   clause::NumBiClause                              0
c   clause::NumBiLearnt                              0
c   clause::NumClause                            80246
c   clause::NumLBD2                              53329
c   clause::NumLearnt                            78724
c   clause::NumReduction                           263
c   clause::NumReRegistration                        0
c   clause::LBD                                     16.524
c   clause::Tier1ClauseRatio                         0.190
c   clause::Tier2ClauseRatio                         0.004
c   state::Vivification                            264
c   state::VivifiedClause                         3151
c   state::VivifiedVar                               0
c   state::NumCycle                                  7
c   state::NumStage                                134
c   state::IntervalScale                             2
c   state::IntervalScaleMax                          7
c   state::ChronologicalBacktrackRate                0.000
c   state::BackjumpLevel                            20.567
c   state::ConflictLevel                            21.800
c   LBD 1 (0.004): 0.000, 0.004, 0.000, 0.000, 0.000, 0.000, 0.000, 0.000
c   LBD 2 (0.031): 0.000, 0.031, 0.000, 0.000, 0.000, 0.000, 0.000, 0.000
c   LBD 3 (0.107): 0.000, 0.000, 0.107, 0.000, 0.000, 0.000, 0.000, 0.000
c   LBD 4 (0.201): 0.000, 0.000, 0.201, 0.000, 0.000, 0.000, 0.000, 0.000
c   LBD 5 (0.250): 0.000, 0.000, 0.250, 0.000, 0.000, 0.000, 0.000, 0.000
c   LBD 6 (0.197): 0.000, 0.000, 0.197, 0.000, 0.000, 0.000, 0.000, 0.000
c   LBD>6 (0.210): 0.000, 0.000, 0.000, 0.199, 0.010, 0.000, 0.000, 0.000
c
s SATISFIABLE
v 1 -2 3 4 5 6 -7 -8 9 -10 -11 -12 13 -14 ...  -360 0
```

```plain
$ dmcr cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
A valid assignment set for cnfs/unif-k3-r4.25-v360-c1530-S1293537826-039.cnf is found in ans_unif-k3-r4.25-v360-c1530-S1293537826-039.cnf
```

#### Verify UNSAT answer with [drat-trim](https://github.com/marijnheule/drat-trim)

If you want to certificate unsatisfiability, use `--certify` or `-c` and use a proof checker like [drat-trim](https://github.com/marijnheule/drat-trim), [Grat](https://www21.in.tum.de/~lammich/grat/), or gratchk, and so on.

Firstly run splr with the certificate option `-c`.

```plain
$ splr -c cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
unif-k3-r4.25-v360-c1530-S1028159446-096.cnf       360,1530 |time:   433.91
 #conflict:    4567454, #decision:      7606131, #propagate:      206567216
  Assignment|#rem:      321, #fix:       28, #elm:       11, prg%:  10.8333
      Clause|Remv:    19906, LBD2:    37637, BinC:      286, Perm:     1403
    Conflict|cLvl:     9.00, bLvl:     7.89,  LBD:     3.72, /cpr: 20057.27
  Luby stage| idx:      172, ti1%:    18.51, ti2%:     0.13, /dpc:     1.07
      LRB(→)| LRB:    29.47, VMTF:    24.14, core:      295, /ppc:    44.30
      Result|file: ./ans_unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
 Certificate|file: proof.drat
s UNSATISFIABLE: cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf
```

Then use `drat-trim`:

```plain
$ drat-trim cnfs/unif-k3-r4.25-v360-c1530-S1028159446-096.cnf proof.drat
c parsing input formula with 360 variables and 1530 clauses
c finished parsing
c detected empty clause; start verification via backward checking
c 1530 of 1530 clauses in core
c 2505800 of 4619164 lemmas in core using 84730284 resolution steps
c 0 RAT lemmas in core; 1532064 redundant literals in core lemmas
s VERIFIED
c verification time: 161.150 seconds
```

### Calling Splr from Rust programs

Since 0.4.0, you can use Splr in your programs. (Here I suppose that you use Rust 2021.)

```rust
use splr::*;

fn main() {
    let v: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]];
    match Certificate::try_from(v) {
        Ok(Certificate::SAT(ans)) => println!("s SATISFIABLE: {:?}", ans),
        Ok(Certificate::UNSAT) => println!("s UNSATISFIABLE"),
        Err(e) => panic!("s UNKNOWN; {}", e),
    }
}
```

Note: As of version 0.18.0, Splr no longer supports incremental mode,
as it is not part of the development direction.

#### sample code from my [sudoku solver](https://github.com/shnarazk/sudoku_sat/)

https://github.com/shnarazk/sudoku_sat/blob/4490b4358e5f3b72803a566323a6c8c196627f92/src/bin/sudoku400.rs#L36-L60

```rust
    let mut solver = Solver::try_from((config, rules.as_ref())).expect("panic");
    for a in setting.iter() {
        solver.add_assignment(*a).expect("panic");
    }
    for ans in solver.iter().take(1) {
        let mut picked = ans.iter().filter(|l| 0 < **l).collect::<Vec<&i32>>();
        for _i in 1..=range {
            for _j in 1..=range {
                let (_i, _j, d, _b) = Cell::decode(*picked.remove(0));
                print!("{:>2} ", d);
            }
            println!();
        }
        println!();
    }
}
```

### Mnemonics used in the progress message

| mnemonic     | meaning                                                                                   |
| ------------ | ----------------------------------------------------------------------------------------- |
| `#var`       | the number of variables used in the given CNF file                                        |
| `#cls`       | the number of clauses used in the given CNF file                                          |
| `time`       | the elapsed CPU time in seconds                                                           |
| `#conflict`  | the number of conflicts                                                                   |
| `#decision`  | the number of decisions                                                                   |
| `#propagate` | the number of propagates (its unit is literal)                                            |
| `#rem`       | the number of remaining variables                                                         |
| `#fix`       | the number of asserted variables (which have been assigned a value at decision level zero) |
| `#elm`       | the number of eliminated variables                                                        |
| `prg%`       | the percentage of `remaining variables / total variables`                                 |
| `Remv`       | the current number of learnt clauses that are not bi-clauses                              |
| `LBD2`       | the accumulated number of learnt clauses which LBDs are 2                                 |
| `BinC`       | the current number of binary learnt clauses                                               |
| `Perm`       | the current number of given clauses and binary learnt clauses                             |
| `cLvl`       | the EMA, Exponential Moving Average, of decision levels at which conflicts occur          |
| `bLvl`       | the EMA of decision levels to which backjumps go                                          |
| `LBD`        | the EMA of LBD of learnt clauses                                                          |
| `/cpr`       | the EMA of conflicts per restart                                                          |
| `idx`        | the current index of Luby sequence                                                        |
| `ti1%`       | the ratio of the learnt clauses which LBDs are in `[3,6]`                                 |
| `ti2%`       | the ratio of the learnt clauses which LBDs are greater than 6                             |
| `/dpc`       | the EMA of decisions per conflict                                                         |
| `LRB(-)`     | the current Var reward scheme is Learning-Rate Based                                      |
| `LongLRB(-)` | the current Var reward scheme is Learning-Rate Based with a very long span                 |
| `VMTF(-)`    | the current Var reward scheme is VMTF                                                     |
| `LongVMTF(-)`| the current Var reward scheme is VMTF with a very long span                               |
| `(→)`        | the active rephasing scheme is `walk`                                                     |
| `(★)`        | the active rephasing scheme is `best`                                                     |
| `(⊥)`        | the active rephasing scheme is `false`                                                    |
| `(⊤)`        | the active rephasing scheme is `true`                                                     |
| `(∼)`        | the active rephasing scheme is `random`                                                   |
| `(¬)`        | the active rephasing scheme is `Inverted`                                                 |
| `(φ)`        | the active rephasing scheme is `polarity`                                                 |
| `LRB`        | the ratio of asserted variables found by LRB in percentages                               |
| `VMTF`       | the ratio of asserted variables found by VMTF in percentages                             |
| `core`       | the number of unreachable variables                                                       |
| `/ppc`       | the EMA of propagations per conflict                                                      |

## Command line options

```plain

A modern CDCL SAT solver in Rust
Activated features: Luby-based clause elimination, Luby-based clause vivification,
 reason-side rewarding, Luby-based re-phasing, trail saving, unsafe access

USAGE:
  splr [FLAGS] [OPTIONS] <cnf-file>
FLAGS:
  -h, --help                Prints help information
  -C, --no-color            Disable coloring
  -q, --quiet               Disable any progress message
  -c, --certify             Writes a DRAT UNSAT certification file
  -H, --heatmap             Shows clause heatmap
  -j, --journal             Shows log about restart stages
  -V, --version             Prints version information
OPTIONS:
      --cl <c-cls-lim>      Soft limit of #clauses (6MC/GB)         0
      --ecl <elm-cls-lim>   Max #lit for clause subsume            64
      --evl <elm-grw-lim>   Grow limit of #cls in var elim.         0
      --evo <elm-var-occ>   Max #cls for var elimination        20000
  -o, --dir <io-outdir>     Output directory                         .
  -p, --proof <io-pfile>    DRAT Cert. filename                 proof.drat
  -r, --result <io-rfile>   Result filename/stdout
  -t, --timeout <timeout>   CPU time limit in sec.               5000
ARGS:
  <cnf-file>    DIMACS CNF file
```

## Solver description

Splr-0.19.0 adopts the following features by default:

- Learning-Rate Based (LRB) var rewarding[4]
- Reason-side var rewarding[4]
- ~~chronological backtrack[5]~~ disabled since 0.12 due to incorrect UNSAT certificates.
- Trail saving[3]
- clause vivification[6]
- Luby series based on the number of conflicts is used as the trigger of
  - restart
  - clause reduction
  - in-processor (clause elimination, subsumption and vivification)
  - re-configuration of var phases and var activities

The following figure explains the flow used in the latest Splr.

![search algorithm in Splr 0.19](https://github.com/user-attachments/assets/2349d8a3-7d10-4369-863f-159e8c83007e)

#### Bibliography

- [1] G. Audemard and L. Simon, "Predicting learnt clauses quality in modern SAT solvers," in _International Joint Conference on Artificial Intelligence 2009_, pp. 399–404, 2009.

- [2] G. Audemard and L. Simon, "Refining restarts strategies for SAT and UNSAT," in _LNCS_, vol.7513, pp.118–126, 2012.

- [3] R. Hickey and F. Bacchus, "Trail Saving on Backtrack", _SAT 2020_, _LNCS_, vol. 12178, pp.46-61, 2020.

- [4] J. H. Liang, V. Ganesh, P. Poupart, and K. Czarnecki, "Learning Rate Based Branching Heuristic for SAT Solvers," in _LNCS_, vol.9710, pp.123–140, 2016.

- [5] A. Nadel and V. Ryvchin, "Chronological Backtracking," in _Theory and Applications of Satisfiability Testing - SAT 2018_, June 2018, pp.111–121, 2018.

- [6] C. Piette, Y. Hamadi, and L. Saïs, "Vivifying propositional clausal formulae," _Front. Artif. Intell. Appl._, vol.178, pp.525–529, 2008.

## License

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at http://mozilla.org/MPL/2.0/.

---

2020-2026, Narazaki Shuji
