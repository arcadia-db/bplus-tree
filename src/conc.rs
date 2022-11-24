use parking_lot::lock_api::{ArcRwLockUpgradableReadGuard, ArcRwLockWriteGuard};
use parking_lot::RawRwLock;

use super::{node::*, typedefs::*};

pub struct SharedLatchInfo<const FANOUT: usize, K: Key, V: Record> {
    pub lock: ArcRwLockUpgradableReadGuard<RawRwLock, Node<FANOUT, K, V>>,
    pub node: NodePtr<FANOUT, K, V>,
}
pub struct ExclusiveLatchInfo<const FANOUT: usize, K: Key, V: Record> {
    pub lock: ArcRwLockWriteGuard<RawRwLock, Node<FANOUT, K, V>>,
    pub node: NodePtr<FANOUT, K, V>,
}

impl<const FANOUT: usize, K: Key, V: Record> SharedLatchInfo<FANOUT, K, V> {
    pub fn upgrade(latch: Self) -> ExclusiveLatchInfo<FANOUT, K, V> {
        ExclusiveLatchInfo {
            lock: ArcRwLockUpgradableReadGuard::upgrade(latch.lock),
            node: latch.node,
        }
    }
}
