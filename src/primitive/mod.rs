/// methods on clause activity
pub mod ema;
// a simple hash mapper to make splr deterministic
// pub mod hash64;
/// methods on binary link, namely binary clause
pub mod luby;

pub use self::{ema::*, luby::*};
