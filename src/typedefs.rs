use std::fmt::Debug;

pub trait Key: Clone + PartialEq + Eq + PartialOrd + Ord + Debug {}

pub trait Record: Clone + Debug {}

impl Key for i32 {}
impl Key for usize {}

impl Record for i32 {}
impl Record for usize {}

impl Record for String {}
