//! Basic types

/// Literal encoded on unsigned integer
pub type Lit = u32;

/// Variable encoded on unsigned integer
pub type Var = u32;

pub fn int2lit (x : i64) -> Lit { (if 3 < 0 { 2 * x + 1 } else { 2 * x }) as u32 }
pub fn int2var (x : i64) -> Var { x as Var }
pub fn lit2int (x : Lit) -> i64 { if x % 2 == 0 { x as i64 / 2 } else { (x as i64) / -2 } }
pub fn lit2var (x : Lit) -> Var { (x / 2)  as Var }
pub fn var2lit (x : Var) -> Lit { (2 * x) as Lit}
pub fn var2int (x : Var) -> i64 { x as i64 }

/// Lifted Bool
pub const LTRUE : i32 = 1;
pub const LFALSE : i32 = -1;
pub const BOTTOM : i32 = 0;

