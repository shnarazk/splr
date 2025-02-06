//! Ordering data by f64 values
use std::cmp::Ordering;

#[derive(Clone, Debug)]
pub struct OrderedProxy<T: Clone + Default + Sized + Ord> {
    pub index: f64,
    pub body: T,
}

impl<T: Clone + Default + Sized + Ord> Default for OrderedProxy<T> {
    fn default() -> Self {
        OrderedProxy {
            index: 0.0,
            body: T::default(),
        }
    }
}

impl<T: Clone + Default + Sized + Ord> PartialEq for OrderedProxy<T> {
    fn eq(&self, other: &OrderedProxy<T>) -> bool {
        self.index == other.index && self.body == other.body
    }
}

impl<T: Clone + Default + Sized + Ord> Eq for OrderedProxy<T> {}

impl<T: Clone + Default + PartialEq + Ord> PartialOrd for OrderedProxy<T> {
    fn partial_cmp(&self, other: &OrderedProxy<T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Clone + Default + PartialEq + Ord> Ord for OrderedProxy<T> {
    fn cmp(&self, other: &OrderedProxy<T>) -> Ordering {
        if let Some(ord) = self.index.partial_cmp(&other.index) {
            ord
        } else {
            match (self.index.is_nan(), other.index.is_nan()) {
                (true, true) => Ordering::Equal,
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => unreachable!(),
            }
        }
    }
}

impl<T: Clone + Default + Sized + Ord> OrderedProxy<T> {
    pub fn new(body: T, index: f64) -> Self {
        OrderedProxy { index, body }
    }
    /// TODO: just use std::cmp::Reverse?
    pub fn new_invert(body: T, rindex: f64) -> Self {
        OrderedProxy {
            index: -rindex,
            body,
        }
    }
    pub fn to(&self) -> T {
        self.body.clone()
    }
    pub fn value(&self) -> f64 {
        self.index
    }
}
