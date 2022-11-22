use std::sync::{RwLockReadGuard, RwLockWriteGuard};

use super::{node::*, typedefs::*};

pub struct SharedLatch<'a, const FANOUT: usize, K: Key, V: Record> {
    pub lock: RwLockReadGuard<'a, Node<FANOUT, K, V>>,
    pub node: NodePtr<FANOUT, K, V>,
}

pub struct ExclusiveLatch<'a, const FANOUT: usize, K: Key, V: Record> {
    pub lock: RwLockWriteGuard<'a, Node<FANOUT, K, V>>,
    pub node: NodePtr<FANOUT, K, V>,
}
