use super::typedefs::*;
use std::sync::{Arc, RwLock, Weak};

const INVALID_NODE_ERROR_MESSAGE: &'static str = "Invalid node encountered!";

pub type NodePtr<const FANOUT: usize, K, T> = Arc<RwLock<Node<FANOUT, K, T>>>;

pub type NodeWeakPtr<const FANOUT: usize, K, T> = Weak<RwLock<Node<FANOUT, K, T>>>;

pub type RecordPtr<T> = Arc<RwLock<T>>;

#[derive(Debug)]
pub struct Leaf<const FANOUT: usize, K: Key, T: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub records: Vec<Option<RecordPtr<T>>>,
    pub parent: Option<NodeWeakPtr<FANOUT, K, T>>,
    pub prev: Option<NodeWeakPtr<FANOUT, K, T>>,
    pub next: Option<NodeWeakPtr<FANOUT, K, T>>,
}

#[derive(Debug)]
pub struct Interior<const FANOUT: usize, K: Key, T: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub parent: Option<NodeWeakPtr<FANOUT, K, T>>,
    pub children: Vec<Option<NodePtr<FANOUT, K, T>>>,
}

#[derive(Default, Debug)]
pub enum Node<const FANOUT: usize, K: Key, T: Record> {
    #[default]
    Invalid,
    Leaf(Leaf<FANOUT, K, T>),
    Interior(Interior<FANOUT, K, T>),
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

impl<const FANOUT: usize, K: Key, T: Record> Node<FANOUT, K, T> {
    pub fn new_leaf() -> Leaf<FANOUT, K, T> {
        assert!(FANOUT > 1);
        Leaf {
            num_keys: 0,
            keys: vec![None; FANOUT],
            records: vec![None; FANOUT],
            parent: None,
            prev: None,
            next: None,
        }
    }

    pub fn new_interior() -> Interior<FANOUT, K, T> {
        assert!(FANOUT > 1);
        Interior {
            num_keys: 0,
            keys: vec![None; FANOUT],
            parent: None,
            children: vec![None; FANOUT + 1],
        }
    }

    create_node_get_fn!(get_leaf, &Self, &Leaf<FANOUT, K, T>, Leaf);
    create_node_get_fn!(get_leaf_mut, &mut Self, &mut Leaf<FANOUT, K, T>, Leaf);
    create_node_get_fn!(get_interior, &Self, &Interior<FANOUT, K, T>, Interior);
    create_node_get_fn!(get_interior_mut, &mut Self, &mut Interior<FANOUT, K, T>, Interior);

    pub(super) fn get_parent(&self) -> Option<NodeWeakPtr<FANOUT, K, T>> {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.parent.clone(),
            Node::Interior(interior) => interior.parent.clone(),
        }
    }

    pub(super) fn set_parent(&mut self, parent: Option<NodePtr<FANOUT, K, T>>) {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => {
                leaf.parent = if let Some(parent) = parent {
                    Some(Arc::downgrade(&parent))
                } else {
                    None
                };
            }
            Node::Interior(interior) => {
                interior.parent = if let Some(parent) = parent {
                    Some(Arc::downgrade(&parent))
                } else {
                    None
                };
            }
        }
    }
}
