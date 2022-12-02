use std::{mem, sync::Arc};

use parking_lot::RwLock;

use crate::typedefs::*;

use super::node::Node;

#[derive(Debug, Clone)]
pub struct Interior<const FANOUT: usize, K: Key, V: Record> {
    pub num_keys: usize,
    pub keys: Vec<Option<K>>,
    pub children: Vec<NodePtr<FANOUT, K, V>>,
}

impl<const FANOUT: usize, K: Key, V: Record> Interior<FANOUT, K, V> {
    pub fn new() -> Self {
        assert!(FANOUT > 1);
        let mut children = Vec::with_capacity(FANOUT + 1);
        for _ in 0..FANOUT + 1 {
            children.push(Node::new_empty());
        }
        Self {
            num_keys: 0,
            keys: vec![None; FANOUT],
            children,
        }
    }

    pub fn insert(&mut self, key: K, child: NodePtr<FANOUT, K, V>) {
        let mut left_idx_in_parent = 0;
        while left_idx_in_parent < self.num_keys
            && self.keys[left_idx_in_parent].as_ref().unwrap() < &key
        {
            left_idx_in_parent += 1
        }

        let mut i = self.num_keys + 1;
        while i > left_idx_in_parent + 1 {
            self.keys.swap(i - 1, i - 2);
            self.children.swap(i, i - 1);
            i -= 1
        }
        self.keys[left_idx_in_parent] = Some(key);
        self.children[left_idx_in_parent + 1] = child;
        self.num_keys += 1;
    }

    pub fn remove(&mut self, right_child: &NodePtr<FANOUT, K, V>) {
        let mut right_child_idx = 0;
        while right_child_idx <= self.num_keys
            && !Arc::ptr_eq(&self.children[right_child_idx], right_child)
        {
            right_child_idx += 1;
        }
        debug_assert_ne!(right_child_idx, self.num_keys + 1);

        self.keys[right_child_idx - 1] = None;
        self.children[right_child_idx] = Node::new_empty();
        for j in right_child_idx - 1..self.num_keys - 1 {
            self.keys.swap(j, j + 1);
            self.children.swap(j + 1, j + 2);
        }
        self.num_keys -= 1;
    }

    pub fn split(&mut self) -> (K, NodePtr<FANOUT, K, V>) {
        let mut new_interior: Interior<FANOUT, K, V> = Self::new();
        let split = (FANOUT + 1) / 2 - 1;

        for i in split + 1..self.num_keys {
            mem::swap(&mut self.keys[i], &mut new_interior.keys[i - split - 1]);
            mem::swap(
                &mut self.children[i],
                &mut new_interior.children[i - split - 1],
            );
        }
        let pushed_key = self.keys[split].as_ref().unwrap().clone();
        mem::swap(
            &mut self.children[FANOUT],
            &mut new_interior.children[self.num_keys - split - 1],
        );
        self.keys[split] = None;

        new_interior.num_keys = self.num_keys - split - 1;
        self.num_keys = split;
        (
            pushed_key,
            Arc::new(RwLock::new(Some(Node::Interior(new_interior)))),
        )
    }

    pub fn borrow_from_successor(
        &mut self,
        successor: &mut Interior<FANOUT, K, V>,
        discriminator_key: K,
    ) -> Option<K> {
        self.keys[self.num_keys] = Some(discriminator_key);
        mem::swap(
            &mut self.children[self.num_keys + 1],
            &mut successor.children[0],
        );

        let replacement_key = successor.keys[0].clone();
        successor.keys[0] = None;
        for i in 1..successor.num_keys {
            successor.keys.swap(i - 1, i);
            successor.children.swap(i - 1, i);
        }
        successor
            .children
            .swap(successor.num_keys - 1, successor.num_keys);
        self.num_keys += 1;
        successor.num_keys -= 1;

        replacement_key
    }

    pub fn borrow_from_predecessor(
        &mut self,
        predecessor: &mut Interior<FANOUT, K, V>,
        discriminator_key: K,
    ) -> Option<K> {
        let mut i = self.num_keys;
        self.children.swap(self.num_keys + 1, self.num_keys);
        while i > 0 {
            self.keys.swap(i, i - 1);
            self.children.swap(i, i - 1);
            i -= 1;
        }
        let replacement_key = predecessor.keys[predecessor.num_keys - 1].clone();
        predecessor.keys[predecessor.num_keys - 1] = None;
        self.keys[0] = Some(discriminator_key);
        mem::swap(
            &mut self.children[0],
            &mut predecessor.children[predecessor.num_keys],
        );

        predecessor.num_keys -= 1;
        self.num_keys += 1;

        replacement_key
    }

    pub fn merge(&mut self, successor: &mut Interior<FANOUT, K, V>, discriminator_key: K) {
        self.keys[self.num_keys] = Some(discriminator_key);
        for j in 0..successor.num_keys {
            mem::swap(
                &mut self.keys[j + self.num_keys + 1],
                &mut successor.keys[j],
            );
        }
        for j in 0..successor.num_keys + 1 {
            mem::swap(
                &mut self.children[j + self.num_keys + 1],
                &mut successor.children[j],
            );
        }
        self.num_keys = self.num_keys + successor.num_keys + 1;
    }
}
