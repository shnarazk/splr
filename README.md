Splr -- SAT Solver for Propositional Logic in Rust
----

## Features

- it based on Glucose 4.1, and uses many ideas in modern SAT solvers like:
  - CDCL
  - glucose-like dynamic blockling/forcing restart
  - ACID for variable activity (instead of VSIDS)
  - Chan Seok heuristic

- Adapts some implementation ideas:
  - watch lists are embedded into a clause vector
  - clause partitioning

## Install

Just clone me, and `cargo install`.

