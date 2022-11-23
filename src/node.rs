use super::typedefs::*;
use core::fmt;
use std::sync::{Arc, RwLock, Weak};

const INVALID_NODE_ERROR_MESSAGE: &str = "Invalid node encountered!";

pub type NodePtr<const FANOUT: usize, K, V> = Arc<RwLock<Node<FANOUT, K, V>>>;

pub type NodeWeakPtr<const FANOUT: usize, K, V> = Weak<RwLock<Node<FANOUT, K, V>>>;

pub type RecordPtr<V> = Arc<RwLock<V>>;

#[derive(Debug, Clone)]
pub struct Leaf<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub records: Vec<Option<RecordPtr<V>>>,
    pub prev: Option<NodeWeakPtr<FANOUT, K, V>>,
    pub next: Option<NodeWeakPtr<FANOUT, K, V>>,
}

#[derive(Debug, Clone)]
pub struct Interior<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub children: Vec<Option<NodePtr<FANOUT, K, V>>>,
}

#[derive(Default, Clone)]
pub enum Node<const FANOUT: usize, K: Key, V: Record> {
    #[default]
    Invalid,
    Leaf(Leaf<FANOUT, K, V>),
    Interior(Interior<FANOUT, K, V>),
}

macro_rules! create_node_get_fn {
    ($name:ident, $param:ty, $ret:ty, $match:ident) => {
        pub(super) fn $name(self: $param) -> Option<$ret> {
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
        assert!(FANOUT > 1);
        Leaf {
            num_keys: 0,
            keys: vec![None; FANOUT],
            records: vec![None; FANOUT],
            prev: None,
            next: None,
        }
    }

    pub fn new_interior() -> Interior<FANOUT, K, V> {
        assert!(FANOUT > 1);
        Interior {
            num_keys: 0,
            keys: vec![None; FANOUT],
            children: vec![None; FANOUT + 1],
        }
    }

    create_node_get_fn!(get_leaf, &Self, &Leaf<FANOUT, K, V>, Leaf);
    create_node_get_fn!(get_leaf_mut, &mut Self, &mut Leaf<FANOUT, K, V>, Leaf);
    create_node_get_fn!(get_interior, &Self, &Interior<FANOUT, K, V>, Interior);
    create_node_get_fn!(get_interior_mut, &mut Self, &mut Interior<FANOUT, K, V>, Interior);

    pub(super) fn is_interior(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Interior(_) => true,
            _ => false,
        }
    }

    pub(super) fn is_underfull(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys < (FANOUT - 1) / 2,
            Node::Interior(interior) => interior.num_keys < (FANOUT + 1) / 2,
        }
    }

    pub(super) fn is_full(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys >= FANOUT - 1,
            Node::Interior(interior) => interior.num_keys >= FANOUT - 1,
        }
    }

    pub(super) fn has_space_for_insert(&self) -> bool {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.num_keys < FANOUT - 1,
            Node::Interior(interior) => interior.num_keys < FANOUT - 1,
        }
    }

    pub(super) fn has_space_for_removal(&self) -> bool {
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
                    records.push(match r {
                        Some(val) => {
                            let lock = val.try_read().ok();
                            lock
                        }
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
                    children.push(match r {
                        Some(val) => {
                            let lock = val.try_read().ok();
                            lock
                        }
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
