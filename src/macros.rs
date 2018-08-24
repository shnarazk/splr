/// In solver's method, use it like
/// ```ignore
/// cref!(self.cv, cid)
/// ```
#[macro_export]
macro_rules! cref {
    ($cv:expr, $val:expr) => {{
        match (&mut $cv, &$val) {
            (v, cid) => &mut v[cid.to_kind()].clauses[cid.to_index()],
        }
    }};
}
