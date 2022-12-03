use crate::typedefs::*;
use core::fmt;
use parking_lot::RwLock;
use std::sync::Arc;

use super::{interior::Interior, leaf::Leaf};

const INVALID_NODE_ERROR_MESSAGE: &str = "Invalid node encountered!";

#[derive(Default, Clone)]
pub enum Node<const FANOUT: usize, K: Key, V: Record> {
    #[default]
    Invalid,
    Leaf(Leaf<FANOUT, K, V>),
    Interior(Interior<FANOUT, K, V>),
}

macro_rules! create_node_get_fn {
    ($name:ident, $param:ty, $ret:ty, $match:ident) => {
        pub fn $name(self: $param) -> Option<$ret> {
            match self {
                Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
                Node::$match(value) => Some(value),
                _ => None,
            }
        }
    };
}

impl<const FANOUT: usize, K: Key, V: Record> Node<FANOUT, K, V> {
    pub fn new_leaf() -> Leaf<FANOUT, K, V> {
        Leaf::new()
    }

    pub fn new_interior() -> Interior<FANOUT, K, V> {
        Interior::new()
    }

    pub fn new_empty() -> NodePtr<FANOUT, K, V> {
        Arc::new(RwLock::new(None))
    }

    pub fn borrow_from_predecessor(
        &mut self,
        predecessor: &mut Node<FANOUT, K, V>,
        discriminator_key: K,
    ) -> Option<K> {
        match &mut *self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.borrow_from_predecessor(predecessor.get_leaf_mut().unwrap()),
            Node::Interior(interior) => interior.borrow_from_predecessor(
                predecessor.get_interior_mut().unwrap(),
                discriminator_key,
            ),
        }
    }
    pub fn borrow_from_successor(
        &mut self,
        successor: &mut Node<FANOUT, K, V>,
        discriminator_key: K,
    ) -> Option<K> {
        match &mut *self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.borrow_from_successor(successor.get_leaf_mut().unwrap()),
            Node::Interior(interior) => interior
                .borrow_from_successor(successor.get_interior_mut().unwrap(), discriminator_key),
        }
    }

    pub fn merge(&mut self, successor: &mut Node<FANOUT, K, V>, discriminator_key: K) {
        match &mut *self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.merge(successor.get_leaf_mut().unwrap()),
            Node::Interior(interior) => {
                interior.merge(successor.get_interior_mut().unwrap(), discriminator_key)
            }
        }
    }

    pub fn is_interior(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Interior(_) => true,
            _ => false,
        }
    }

    create_node_get_fn!(get_leaf, &Self, &Leaf<FANOUT, K, V>, Leaf);
    create_node_get_fn!(get_leaf_mut, &mut Self, &mut Leaf<FANOUT, K, V>, Leaf);
    create_node_get_fn!(get_interior, &Self, &Interior<FANOUT, K, V>, Interior);
    create_node_get_fn!(get_interior_mut, &mut Self, &mut Interior<FANOUT, K, V>, Interior);

    pub fn get_num_keys(&self) -> usize {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys,
            Node::Interior(node) => node.num_keys,
        }
    }

    pub fn is_underfull(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys < (FANOUT - 1) / 2,
            Node::Interior(interior) => interior.num_keys < FANOUT / 2,
        }
    }

    // pub fn is_overfull(&self) -> bool {
    //     match self {
    //         Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
    //         Node::Leaf(leaf) => leaf.num_keys >= FANOUT,
    //         Node::Interior(interior) => interior.num_keys >= FANOUT,
    //     }
    // }

    pub fn has_space_for_insert(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys < FANOUT - 1,
            Node::Interior(interior) => interior.num_keys < FANOUT - 1,
        }
    }

    pub fn has_space_for_removal(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys > (FANOUT - 1) / 2,
            Node::Interior(interior) => interior.num_keys > FANOUT / 2,
        }
    }
}

impl<const FANOUT: usize, K: Key, V: Record> fmt::Debug for Node<FANOUT, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Invalid => f.debug_struct("Invalid").finish(),
            Node::Leaf(leaf) => {
                let keys = leaf.keys[..leaf.keys.len() - 1]
                    .iter()
                    .map(|x| x.as_ref())
                    .collect::<Vec<Option<&K>>>();

                let mut records = vec![];
                for r in &leaf.records[..leaf.records.len() - 1] {
                    records.push(match r.try_read() {
                        Some(val) => val.clone(),
                        None => None,
                    })
                }

                f.debug_struct("Leaf")
                    .field("num_keys", &leaf.num_keys)
                    .field("keys", &keys)
                    .field("records", &records)
                    // .field("prev", &leaf.prev)
                    // .field("next", &leaf.next)
                    // .field("parent", &leaf.parent)
                    .finish()
            }
            Node::Interior(node) => {
                let keys = node.keys[..node.keys.len() - 1]
                    .iter()
                    .map(|x| x.as_ref())
                    .collect::<Vec<Option<&K>>>();

                let mut children = vec![];
                for r in &node.children[..node.children.len() - 1] {
                    children.push(match r.try_read() {
                        Some(val) => val.clone(),
                        None => None,
                    })
                }
                f.debug_struct("Interior")
                    .field("num_keys", &node.num_keys)
                    .field("keys", &keys)
                    .field("children", &children)
                    // .field("parent", &node.parent)
                    .finish()
            }
        }
    }
}
