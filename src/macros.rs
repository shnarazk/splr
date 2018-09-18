/// In solver's method, use it like
/// ```ignore
/// cref!(self.cv, cid)
/// ```
#[macro_export]
macro_rules! iref {
    ($cv: expr, $val: expr) => {{
        match (&$cv, $val) {
            (v, cid) => &v[cid.to_kind()].clauses[cid.to_index()],
        }
    }};
}

macro_rules! mref {
    ($cv: expr, $val: expr) => {{
        match (&mut $cv, $val) {
            (v, cid) => &mut v[cid.to_kind()].clauses[cid.to_index()],
        }
    }};
}

macro_rules! lindex {
    ($c:expr, $val:expr) => {{
        match (&$c, $val) {
            (c, i) => if i < 2 { c.lit[i] } else { c.lits[i - 2] },
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
            }}
    }}
}
