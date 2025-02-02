use {crate::types::*, std::collections::BinaryHeap};

#[derive(Clone, Debug, Default)]
pub struct VarActivityManager {
    pub(crate) activity_decay: f64,
    pub(crate) heap: BinaryHeap<OrderedProxy<VarId>>,
    pub(crate) tick: usize,
}

pub trait VarActivityManagerIF<'a> {
    // fn new(conf: &Config, cnf: &CNFDescription) -> Self;
    fn select_var(&mut self) -> Option<VarId>;
    fn insert(&mut self, vi: &'a Var<'a>);
    fn clear(&mut self);
    fn remove(&mut self, v: &'a Var<'a>);
    fn add_activity(&mut self, v: &mut Var<'a>);
    // fn update_activity_decay(&'a mut self);
}

impl<'a> Instantiate for VarActivityManager {
    fn instantiate(_conf: &Config, _cnf: &CNFDescription) -> Self {
        let heap = BinaryHeap::new();
        VarActivityManager {
            activity_decay: 0.9,
            heap,
            tick: 0,
        }
    }
}

impl<'a> VarActivityManagerIF<'a> for VarActivityManager {
    fn select_var(&mut self) -> Option<VarId> {
        self.heap.pop().map(|x| x.to())
    }
    fn insert(&mut self, v: &'a Var<'a>) {
        self.heap.push(OrderedProxy::new(v.id, v.activity));
    }

    fn clear(&mut self) {
        self.heap.clear();
    }

    fn remove(&mut self, v: &Var<'a>) {
        self.heap.retain(|x| x.to() != v.id);
    }

    fn add_activity(&mut self, _v: &mut Var<'a>) {
        unimplemented!()
    }
}

impl VarActivityManager {
    pub fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
    pub(crate) fn select_rephasing_target(&self) -> () {
        todo!()
    }
    // pub(crate) fn select_decision_literal(&mut self) -> Lit<'a> {
    //     todo!()
    // }
    pub fn update_activity_decay(&mut self, _val: f64) {
        todo!()
    }
}
