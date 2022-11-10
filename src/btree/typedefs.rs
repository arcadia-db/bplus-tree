use std::fmt::Debug;

pub trait Key: Clone + PartialEq + Eq + PartialOrd + Ord + Debug {}

pub trait Record: Clone + Debug {}
