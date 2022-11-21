use std::sync::{RwLockReadGuard, RwLockWriteGuard};

use super::{node::*, typedefs::*};

pub struct TraversalSharedResult<'a, const FANOUT: usize, K: Key, V: Record> {
    pub retained_locks: Vec<RwLockReadGuard<'a, Node<FANOUT, K, V>>>,
    // to make sure the referenced nodes aren't cleared
    pub retained_nodes: Vec<NodePtr<FANOUT, K, V>>,
}

impl<'a, const FANOUT: usize, K: Key, V: Record> TraversalSharedResult<'a, FANOUT, K, V> {
    pub fn empty() -> Self {
        Self {
            retained_locks: vec![],
            retained_nodes: vec![],
        }
    }

    pub fn release_parent(&mut self) {
        if self.retained_locks.len() > 1 {
            drop(self.retained_locks.remove(0));
            self.retained_nodes.remove(0);
        }
    }

    pub fn release_leaf(&mut self) {
        if !self.retained_locks.is_empty() {
            drop(self.retained_locks.pop());
            self.retained_nodes.pop();
        }
    }
}

pub struct TraversalExclusiveResult<'a, const FANOUT: usize, K: Key, V: Record> {
    pub retained_locks: Vec<RwLockWriteGuard<'a, Node<FANOUT, K, V>>>,
    pub retained_nodes: Vec<NodePtr<FANOUT, K, V>>,
}

impl<'a, const FANOUT: usize, K: Key, V: Record> TraversalExclusiveResult<'a, FANOUT, K, V> {
    pub fn empty() -> Self {
        Self {
            retained_locks: vec![],
            retained_nodes: vec![],
        }
    }
}

// fn get_leaf_shared(&self, key: &K) -> TraversalSharedResult<FANOUT, K, V> {
//     let mut current_node = self.root.clone().unwrap();
//     let mut lock = self.root.as_ref().unwrap().read().unwrap();
//     let mut s = vec![];
//     let mut retained_nodes = vec![];

//     while lock.is_interior() {
//         // Keep the data in node around by holding on to this `Arc`.
//         retained_nodes.push(current_node);

//         current_node = {
//             let mut i = 0;
//             let node = lock.get_interior().unwrap();
//             while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
//                 i += 1;
//             }
//             node.children[i].as_ref().unwrap().clone()
//         };

//         s.push(lock);

//         // lock the next node
//         // We are going to move out of node while this lock is still around,
//         // but since we kept the data around it's ok.
//         lock = unsafe { mem::transmute(current_node.read().unwrap()) };

//         if lock.is_interior() {
//             drop(s.pop());
//         }
//     }
//     retained_nodes.push(current_node);

//     TraversalSharedResult {
//         retained_locks: s,
//         _retained_nodes: retained_nodes,
//     }
// }
