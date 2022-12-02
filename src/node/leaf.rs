use std::{
    mem,
    sync::{Arc, Weak},
};

use parking_lot::RwLock;

use crate::typedefs::*;

use super::node::Node;

#[derive(Debug, Clone)]
pub struct Leaf<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub records: Vec<RecordPtr<V>>,
    pub prev: NodeWeakPtr<FANOUT, K, V>,
    pub next: NodeWeakPtr<FANOUT, K, V>,
}

impl<const FANOUT: usize, K: Key, V: Record> Leaf<FANOUT, K, V> {
    pub fn new() -> Self {
        assert!(FANOUT > 1);
        let mut records = Vec::with_capacity(FANOUT + 1);
        for _ in 0..FANOUT + 1 {
            records.push(Arc::new(RwLock::new(None)));
        }
        Self {
            num_keys: 0,
            keys: vec![None; FANOUT],
            records,
            prev: Weak::new(),
            next: Weak::new(),
        }
    }

    pub fn insert(&mut self, key: K, record: V) {
        let mut insertion_idx = 0;
        while insertion_idx < self.num_keys && key > *self.keys[insertion_idx].as_ref().unwrap() {
            insertion_idx += 1
        }

        // if it exists, just update the record
        if insertion_idx < self.num_keys && *self.keys[insertion_idx].as_ref().unwrap() == key {
            self.records[insertion_idx] = Arc::new(RwLock::new(Some(record)));
            return;
        }

        let mut i = self.num_keys;
        while i > insertion_idx {
            self.keys.swap(i, i - 1);
            self.records.swap(i, i - 1);
            i -= 1
        }
        self.keys[insertion_idx] = Some(key);
        self.records[insertion_idx] = Arc::new(RwLock::new(Some(record)));
        self.num_keys += 1;
    }

    pub fn remove(&mut self, key: &K) {
        let mut i = 0;
        while i < self.num_keys && self.keys[i].as_ref().unwrap() != key {
            i += 1;
        }
        if i == self.num_keys {
            return;
        }

        self.keys[i] = None;
        self.records[i] = Arc::new(RwLock::new(None));
        for j in i..self.num_keys - 1 {
            self.keys.swap(j, j + 1);
            self.records.swap(j, j + 1);
        }
        self.num_keys -= 1;
    }

    pub fn split(&mut self, leaf_node: NodePtr<FANOUT, K, V>) -> (K, NodePtr<FANOUT, K, V>) {
        let mut new_leaf = Self::new();
        let split = FANOUT / 2;

        for i in split..self.num_keys {
            mem::swap(&mut new_leaf.keys[i - split], &mut self.keys[i]);
            mem::swap(&mut new_leaf.records[i - split], &mut self.records[i]);
        }

        new_leaf.num_keys = self.num_keys - split;
        self.num_keys = split;

        let new_key = new_leaf.keys[0].clone().unwrap();
        new_leaf.prev = Arc::downgrade(&leaf_node);
        new_leaf.next = self.next.clone();

        let new_leaf_node = Arc::new(RwLock::new(Some(Node::Leaf(new_leaf))));
        self.next = Arc::downgrade(&new_leaf_node);

        (new_key, new_leaf_node)
    }

    pub fn borrow_from_successor(&mut self, successor: &mut Leaf<FANOUT, K, V>) -> Option<K> {
        mem::swap(&mut self.keys[self.num_keys], &mut successor.keys[0]);
        mem::swap(&mut self.records[self.num_keys], &mut successor.records[0]);
        for i in 1..successor.num_keys {
            successor.keys.swap(i - 1, i);
            successor.records.swap(i - 1, i);
        }
        self.num_keys += 1;
        successor.num_keys -= 1;

        successor.keys[0].clone()
    }

    pub fn borrow_from_predecessor(&mut self, predecessor: &mut Leaf<FANOUT, K, V>) -> Option<K> {
        let mut i = self.num_keys;
        while i > 0 {
            self.keys.swap(i, i - 1);
            self.records.swap(i, i - 1);
            i -= 1;
        }
        mem::swap(
            &mut self.keys[0],
            &mut predecessor.keys[predecessor.num_keys - 1],
        );
        mem::swap(
            &mut self.records[0],
            &mut predecessor.records[predecessor.num_keys - 1],
        );
        predecessor.num_keys -= 1;
        self.num_keys += 1;

        self.keys[0].clone()
    }

    pub fn merge(&mut self, successor: &mut Leaf<FANOUT, K, V>) {
        for i in 0..successor.num_keys {
            mem::swap(&mut self.keys[i + self.num_keys], &mut successor.keys[i]);
            mem::swap(
                &mut self.records[i + self.num_keys],
                &mut successor.records[i],
            );
        }
        self.num_keys += successor.num_keys;
        self.next = successor.next.clone();
    }
}
