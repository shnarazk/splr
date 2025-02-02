use {
    super::ClauseId,
    crate::types::*,
    std::{
        collections::HashMap,
        ops::{Index, IndexMut},
    },
};

/// storage of binary links
pub type BinaryLinkList<'a> = Vec<(Lit<'a>, ClauseId)>;

impl<'a> Index<Lit<'a>> for Vec<BinaryLinkList<'a>> {
    type Output = BinaryLinkList<'a>;
    #[inline]
    fn index(&self, l: Lit<'a>) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl<'a> IndexMut<Lit<'a>> for Vec<BinaryLinkList<'a>> {
    #[inline]
    fn index_mut(&mut self, l: Lit<'a>) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[usize::from(l)]
    }
}

/// storage with mapper to `ClauseId` of binary links
#[derive(Clone, Debug, Default)]
pub struct BinaryLinkDB<'a> {
    hash: HashMap<(Lit<'a>, Lit<'a>), ClauseId>,
    list: Vec<BinaryLinkList<'a>>,
}

impl Instantiate for BinaryLinkDB<'_> {
    fn instantiate(_conf: &Config, cnf: &CNFDescription) -> Self {
        let num_lit = 2 * (cnf.num_of_variables + 1);
        BinaryLinkDB {
            hash: HashMap::new(),
            list: vec![Vec::new(); num_lit],
        }
    }
    fn handle(&mut self, _e: SolverEvent) {}
}

pub trait BinaryLinkIF<'a> {
    /// add a mapping from a pair of Lit to a `ClauseId`
    fn add(&'a mut self, lit0: Lit<'a>, lit1: Lit<'a>, cid: ClauseId);
    /// remove a pair of `Lit`s
    fn remove(&'a mut self, lit0: Lit<'a>, lit1: Lit<'a>) -> MaybeInconsistent;
    /// return 'ClauseId` linked from a pair of `Lit`s
    fn search(&'a self, lit0: Lit<'a>, lit1: Lit<'a>) -> Option<&'a ClauseId>;
    /// return the all links that include `Lit`.
    /// Note this is not a `watch_list`. The other literal has an opposite phase.
    fn connect_with(&'a self, lit: Lit<'a>) -> &'a BinaryLinkList<'a>;
    /// add new var
    fn add_new_var(&'a mut self);
    // /// sort links based on var activities
    // fn reorder(&mut self, asg: &impl AssignIF);
}

impl<'a> BinaryLinkIF<'a> for BinaryLinkDB<'a> {
    fn add(&'a mut self, lit0: Lit<'a>, lit1: Lit<'a>, cid: ClauseId) {
        let l0 = lit0.min(lit1);
        let l1 = lit0.max(lit1);
        self.hash.insert((l0, l1), cid);
        self.list[lit0].push((lit1, cid));
        self.list[lit1].push((lit0, cid));
    }
    fn remove(&'a mut self, lit0: Lit<'a>, lit1: Lit<'a>) -> MaybeInconsistent {
        let l0 = lit0.min(lit1);
        let l1 = lit0.max(lit1);
        self.hash.remove(&(l0, l1));
        self.list[lit0].delete_unstable(|p| p.0 == lit1);
        self.list[lit1].delete_unstable(|p| p.0 == lit0);
        Ok(())
    }
    fn search(&'a self, lit0: Lit<'a>, lit1: Lit<'a>) -> Option<&'a ClauseId> {
        let l0 = lit0.min(lit1);
        let l1 = lit0.max(lit1);
        self.hash.get(&(l0, l1))
    }
    fn connect_with(&'a self, lit: Lit<'a>) -> &'a BinaryLinkList<'a> {
        &self.list[lit]
    }
    fn add_new_var(&'a mut self) {
        for _ in 0..2 {
            self.list.push(Vec::new());
        }
    }
    /*
    fn reorder(&mut self, asg: &impl AssignIF) {
        let nv = self.list.len() / 2;
        let thr: f64 = (1usize..nv).map(|i| asg.activity(i)).sum::<f64>()
            / (1usize..nv)
                .filter(|i| {
                    !asg.var(*i).is(FlagVar::ELIMINATED)
                        && asg.reason(*i) != AssignReason::Decision(0)
                })
                .count() as f64;
        'next_lit: for (l, vec) in self.list.iter_mut().enumerate().skip(2) {
            if asg.var(Lit::from(l).vi()).is(FlagVar::ELIMINATED) {
                continue 'next_lit;
            }
            if 0.5 * thr <= asg.activity(Lit::from(l).vi()) {
                vec.sort_by_cached_key(|p|
                                       (asg.activity(p.0.vi()) * -100_000.0) as isize);
            } else {
                // Run just the first stage of quick sort.
                let len = vec.len();
                let mut i = 0;
                let mut j = len;
                while i < j {
                    loop {
                        if len == i {
                            continue 'next_lit;
                        }
                        if asg.activity(vec[i].0.vi()) < thr {
                            break;
                        }
                        i += 1;
                    }
                    loop {
                        if j == 0 {
                            continue 'next_lit;
                        }
                        j -= 1;
                        if thr < asg.activity(vec[j].0.vi()) {
                            break;
                        }
                    }
                    vec.swap(i, j);
                    i += 1;
                }
            }
        }
    }
    */
}
