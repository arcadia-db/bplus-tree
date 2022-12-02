use std::{
    fmt::Debug,
    sync::{Arc, Weak},
};

use parking_lot::RwLock;

use crate::node::node::Node;

pub trait Key: Clone + PartialOrd + Debug {}

pub trait Record: Clone + Debug {}

impl Key for i32 {}
impl Key for usize {}

impl Record for i32 {}
impl Record for usize {}

impl Record for String {}

pub type NodePtr<const FANOUT: usize, K, V> = Arc<RwLock<Option<Node<FANOUT, K, V>>>>;

pub type NodeWeakPtr<const FANOUT: usize, K, V> = Weak<RwLock<Option<Node<FANOUT, K, V>>>>;

pub type RecordPtr<V> = Arc<RwLock<Option<V>>>;
