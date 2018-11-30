/// In solver's method, use it like
/// ```ignore
/// cref!(self.cv, cid)
/// ```
#[macro_export]
macro_rules! clause {
    ($cv: expr, $val: expr) => {{
        match (&$cv, $val) {
            (v, cid) => &v[cid.to_kind()].head[cid.to_index()],
        }
    }};
}

macro_rules! clause_mut {
    ($cv: expr, $val: expr) => {{
        match (&mut $cv, $val) {
            (v, cid) => &mut v[cid.to_kind()].head[cid.to_index()],
        }
    }};
}

#[allow(unused_macros)]
/// WARNING: call `set_flag(ClauseFlag::Locked)` by yourself after this function.
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
