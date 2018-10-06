/// In solver's method, use it like
/// ```ignore
/// cref!(self.cv, cid)
/// ```
#[macro_export]
macro_rules! clause_head {
    ($cv: expr, $val: expr) => {{
        match (&$cv, $val) {
            (v, cid) => &v[cid.to_kind()].head[cid.to_index()],
        }
    }};
}

macro_rules! clause_body {
    ($cv: expr, $val: expr) => {{
        match (&$cv, $val) {
            (v, cid) => &v[cid.to_kind()].body[cid.to_index()],
        }
    }};
}

macro_rules! clause_head_mut {
    ($cv: expr, $val: expr) => {{
        match (&mut $cv, $val) {
            (v, cid) => &mut v[cid.to_kind()].head[cid.to_index()],
        }
    }};
}

macro_rules! clause_body_mut {
    ($cv: expr, $val: expr) => {{
        match (&mut $cv, $val) {
            (v, cid) => &mut v[cid.to_kind()].body[cid.to_index()],
        }
    }};
}

// macro_rules! lindex {
//     ($h: expr, $b: expr, $val: expr) => {{
//         match (&$h, &$b, $val) {
//             (h, b, i) => if i < 2 {
//                 h.lit[i]
//             } else {
//                 b.lits[i - 2]
//             },
//         }
//     }};
// }

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
