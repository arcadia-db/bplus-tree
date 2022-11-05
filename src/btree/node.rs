use std::sync::{Arc, RwLock, Weak};

const FANOUT: usize = 2;

pub trait Key: PartialEq + PartialOrd {}

pub trait Record {}

pub type NodePtr<K, T> = Arc<RwLock<Node<K, T>>>;

pub type NodeWeakPtr<K, T> = Weak<RwLock<Node<K, T>>>;

pub type RecordPtr<T> = Arc<RwLock<T>>;

#[derive(Debug)]
pub struct Leaf<K: Key, V: Record> {
    pub size: usize,
    pub keys: [Option<K>; FANOUT],
    pub records: [Option<RecordPtr<V>>; FANOUT],
    pub parent: Option<NodeWeakPtr<K, V>>,
    pub prev: Option<NodeWeakPtr<K, V>>,
    pub next: Option<NodeWeakPtr<K, V>>,
}

#[derive(Debug)]
pub struct Interior<K: Key, V: Record> {
    pub size: usize,
    pub keys: [Option<K>; FANOUT],
    pub children: [Option<NodePtr<K, V>>; FANOUT + 1],
}

#[derive(Debug, Default)]
pub enum Node<K: Key, V: Record> {
    #[default]
    Invalid,
    Leaf(Leaf<K, V>),
    Interior(Interior<K, V>),
}

impl<K: Key, V: Record> Node<K, V> {
    pub(super) fn leaf(&self) -> Option<&Leaf<K, V>> {
        if let Node::Invalid = self {
            panic!("Invalid Node encountered while accessing leaf!")
        }

        if let Node::Leaf(leaf) = self {
            Some(leaf)
        } else {
            None
        }
    }

    pub(super) fn leaf_mut(&mut self) -> Option<&mut Leaf<K, V>> {
        if let Node::Invalid = self {
            panic!("Invalid Node encountered while accessing leaf!")
        }

        if let Node::Leaf(leaf) = self {
            Some(leaf)
        } else {
            None
        }
    }

    pub(super) fn unwrap_leaf(&self) -> &Leaf<K, V> {
        self.leaf().unwrap()
    }

    pub(super) fn unwrap_leaf_mut(&mut self) -> &mut Leaf<K, V> {
        self.leaf_mut().unwrap()
    }

    pub(super) fn interior(&self) -> Option<&Interior<K, V>> {
        if let Node::Invalid = self {
            panic!("Invalid Node encountered while accessing interior!")
        }

        if let Node::Interior(interior) = self {
            Some(interior)
        } else {
            None
        }
    }

    pub(super) fn unwrap_interior(&self) -> &Interior<K, V> {
        self.interior().unwrap()
    }

    pub(super) fn interior_mut(&mut self) -> Option<&mut Interior<K, V>> {
        if let Node::Invalid = self {
            panic!("Invalid Node encountered while accessing interior!")
        }

        if let Node::Interior(interior) = self {
            Some(interior)
        } else {
            None
        }
    }

    pub(super) fn unwrap_interior_mut(&mut self) -> &mut Interior<K, V> {
        self.interior_mut().unwrap()
    }
}
