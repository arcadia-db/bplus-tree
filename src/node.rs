use super::typedefs::*;
use core::fmt;
use parking_lot::RwLock;
use std::sync::{Arc, Weak};

const INVALID_NODE_ERROR_MESSAGE: &str = "Invalid node encountered!";

pub type NodePtr<const FANOUT: usize, K, V> = Arc<RwLock<Option<Node<FANOUT, K, V>>>>;

pub type NodeWeakPtr<const FANOUT: usize, K, V> = Weak<RwLock<Option<Node<FANOUT, K, V>>>>;

pub type RecordPtr<V> = Arc<RwLock<Option<V>>>;

#[derive(Debug, Clone)]
pub struct Leaf<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub records: Vec<RecordPtr<V>>,
    pub prev: NodeWeakPtr<FANOUT, K, V>,
    pub next: NodeWeakPtr<FANOUT, K, V>,
}

#[derive(Debug, Clone)]
pub struct Interior<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub children: Vec<NodePtr<FANOUT, K, V>>,
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
        let mut records = Vec::with_capacity(FANOUT + 1);
        for _ in 0..FANOUT + 1 {
            records.push(Arc::new(RwLock::new(None)));
        }
        Leaf {
            num_keys: 0,
            keys: vec![None; FANOUT],
            records,
            prev: Weak::new(),
            next: Weak::new(),
        }
    }

    pub fn new_interior() -> Interior<FANOUT, K, V> {
        assert!(FANOUT > 1);
        let mut children = Vec::with_capacity(FANOUT + 1);
        for _ in 0..FANOUT + 1 {
            children.push(Self::new_empty());
        }
        Interior {
            num_keys: 0,
            keys: vec![None; FANOUT],
            children,
        }
    }

    pub fn new_empty() -> NodePtr<FANOUT, K, V> {
        Arc::new(RwLock::new(None))
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

    // pub(super) fn is_underfull(&self) -> bool {
    //     match self {
    //         Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
    //         Node::Leaf(leaf) => leaf.num_keys < (FANOUT - 1) / 2,
    //         Node::Interior(interior) => interior.num_keys < FANOUT / 2,
    //     }
    // }

    // pub(super) fn is_overfull(&self) -> bool {
    //     match self {
    //         Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
    //         Node::Leaf(leaf) => leaf.num_keys >= FANOUT,
    //         Node::Interior(interior) => interior.num_keys >= FANOUT,
    //     }
    // }

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
