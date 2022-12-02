use parking_lot::lock_api::{ArcRwLockReadGuard, ArcRwLockWriteGuard};
use parking_lot::RawRwLock;

use crate::node::node::Node;

use super::typedefs::*;

pub struct SharedLatchInfo<const FANOUT: usize, K: Key, V: Record> {
    pub lock: ArcRwLockReadGuard<RawRwLock, Option<Node<FANOUT, K, V>>>,
    pub node: NodePtr<FANOUT, K, V>,
}
pub struct ExclusiveLatchInfo<const FANOUT: usize, K: Key, V: Record> {
    pub lock: ArcRwLockWriteGuard<RawRwLock, Option<Node<FANOUT, K, V>>>,
    pub node: NodePtr<FANOUT, K, V>,
}

// impl<const FANOUT: usize, K: Key, V: Record> SharedLatchInfo<FANOUT, K, V> {
//     pub fn upgrade(latch: Self) -> ExclusiveLatchInfo<FANOUT, K, V> {
//         ExclusiveLatchInfo {
//             lock: ArcRwLockReadGuard::upgrade(latch.lock),
//             node: latch.node,
//         }
//     }
// }
