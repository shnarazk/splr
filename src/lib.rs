//! This is a SAT solver in Rust.

#[allow(unused_macros)]
macro_rules! uenqueue {
    ($vs: expr, $tr: expr, $tl: expr, $lit: expr, $cid: expr) => {{
        match (&$vs, &mut $tr, &$tl, $lit, $cid) {
            (vs, tr, tl, lit, cid) => {
                let mut v = &mut vs[lit.vi()];
                v.assign = lit.lbool();
                v.level = tl.len();
                v.reason = cid;
                tr.push(lit);
            }
        }
    }};
}

// /// Subsumption-based clause/var eliminaiton
/// Assignment management
pub mod assign;
/// Clause
pub mod clause;
/// Configuration
pub mod config;
/// In-process elimination
pub mod eliminator;
/// Implementation on solver restart.
pub mod restart;
/// struct Solver
pub mod solver;
/// various data for SAT solving
pub mod state;
/// Traits
pub mod traits;
/// Plumping layer.
pub mod types;
/// validates
pub mod validator;
/// Var
pub mod var;
