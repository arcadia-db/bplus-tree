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
    pub parent: Option<NodeWeakPtr<FANOUT, K, V>>,
    pub prev: Option<NodeWeakPtr<FANOUT, K, V>>,
    pub next: Option<NodeWeakPtr<FANOUT, K, V>>,
}

#[derive(Debug, Clone)]
pub struct Interior<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub parent: Option<NodeWeakPtr<FANOUT, K, V>>,
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
            parent: None,
            prev: None,
            next: None,
        }
    }

    pub fn new_interior() -> Interior<FANOUT, K, V> {
        assert!(FANOUT > 1);
        Interior {
            num_keys: 0,
            keys: vec![None; FANOUT],
            parent: None,
            children: vec![None; FANOUT + 1],
        }
    }

    create_node_get_fn!(get_leaf, &Self, &Leaf<FANOUT, K, V>, Leaf);
    create_node_get_fn!(get_leaf_mut, &mut Self, &mut Leaf<FANOUT, K, V>, Leaf);
    create_node_get_fn!(get_interior, &Self, &Interior<FANOUT, K, V>, Interior);
    create_node_get_fn!(get_interior_mut, &mut Self, &mut Interior<FANOUT, K, V>, Interior);

    pub(super) fn get_parent(&self) -> Option<NodeWeakPtr<FANOUT, K, V>> {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.parent.clone(),
            Node::Interior(interior) => interior.parent.clone(),
        }
    }

    pub(super) fn set_parent(&mut self, parent: Option<NodePtr<FANOUT, K, V>>) {
        match self {
            Node::Invalid => panic!("{}", INVALID_NODE_ERROR_MESSAGE),
            Node::Leaf(leaf) => leaf.parent = parent.map(|parent| Arc::downgrade(&parent)),
            Node::Interior(interior) => {
                interior.parent = parent.map(|parent| Arc::downgrade(&parent))
            }
        }
    }
}

pub trait LockInClosure<T> {
    fn safe_read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R;

    fn safe_write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R;
}

impl<T> LockInClosure<T> for Option<Arc<RwLock<T>>> {
    fn safe_read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let lock = self.as_ref().unwrap().read().unwrap();
        f(&*lock)
    }

    fn safe_write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut lock = self.as_ref().unwrap().write().unwrap();
        f(&mut *lock)
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
                            if lock.is_none() {
                                None
                            } else {
                                Some(lock.unwrap().clone())
                            }
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
                            if lock.is_none() {
                                None
                            } else {
                                Some(lock.unwrap().clone())
                            }
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
