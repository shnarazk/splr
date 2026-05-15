//! Ordering data by f64 values
use std::cmp::Ordering;

#[derive(Clone, Debug)]
pub struct SortKey<T: Clone + Default + Sized + Ord> {
    index: f64,
    body: T,
}

impl<T: Clone + Default + Sized + Ord> Default for SortKey<T> {
    fn default() -> Self {
        SortKey {
            index: 0.0,
            body: T::default(),
        }
    }
}

impl<T: Clone + Default + Sized + Ord> PartialEq for SortKey<T> {
    fn eq(&self, other: &SortKey<T>) -> bool {
        self.index == other.index && self.body == other.body
    }
}

impl<T: Clone + Default + Sized + Ord> Eq for SortKey<T> {}

impl<T: Clone + Default + PartialEq + Ord> PartialOrd for SortKey<T> {
    fn partial_cmp(&self, other: &SortKey<T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Clone + Default + PartialEq + Ord> Ord for SortKey<T> {
    fn cmp(&self, other: &SortKey<T>) -> Ordering {
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

impl<T: Clone + Default + Sized + Ord> SortKey<T> {
    pub fn new(body: T, index: f64) -> Self {
        SortKey { index, body }
    }
    /// TODO: just use std::cmp::Reverse?
    pub fn new_invert(body: T, rindex: f64) -> Self {
        SortKey {
            index: -rindex,
            body,
        }
    }
    #[inline]
    pub fn to(&self) -> T {
        self.body.clone()
    }
    #[inline]
    pub fn value(&self) -> f64 {
        self.index
    }
}
