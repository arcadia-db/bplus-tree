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

    pub fn search(&self, key: &K) -> Option<RecordPtr<V>> {
        for i in 0..self.num_keys {
            if *key == *self.keys[i].as_ref().unwrap() {
                return Some(self.records[i].clone());
            }
        }
        None
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_leaf() {
        let leaf = Leaf::<3, i32, i32>::new();
        assert_eq!(leaf.num_keys, 0);
        assert_eq!(leaf.keys, vec![None, None, None]);
        assert_eq!(leaf.records.len(), 4);

        for record in leaf.records {
            assert_eq!(*record.read(), None);
        }

        assert!(leaf.prev.upgrade().is_none());
        assert!(leaf.next.upgrade().is_none());
    }

    #[test]
    fn test_insert() {
        let mut leaf = Leaf::<5, i32, i32>::new();
        leaf.insert(4, 5);

        assert_eq!(leaf.keys[0], Some(4));
        assert_eq!(*leaf.records[0].read(), Some(5));
        assert_eq!(leaf.num_keys, 1);

        // insert before 4
        leaf.insert(2, 2);
        assert_eq!(leaf.keys, vec![Some(2), Some(4), None, None, None]);
        assert_eq!(*leaf.records[0].read(), Some(2));
        assert_eq!(*leaf.records[1].read(), Some(5));
        assert_eq!(leaf.num_keys, 2);

        // insert in between
        leaf.insert(3, 8);
        assert_eq!(leaf.keys, vec![Some(2), Some(3), Some(4), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(2));
        assert_eq!(*leaf.records[1].read(), Some(8));
        assert_eq!(*leaf.records[2].read(), Some(5));
        assert_eq!(leaf.num_keys, 3);

        // insert at end
        leaf.insert(8, 9);
        assert_eq!(leaf.keys, vec![Some(2), Some(3), Some(4), Some(8), None]);
        assert_eq!(*leaf.records[0].read(), Some(2));
        assert_eq!(*leaf.records[1].read(), Some(8));
        assert_eq!(*leaf.records[2].read(), Some(5));
        assert_eq!(*leaf.records[3].read(), Some(9));
        assert_eq!(leaf.num_keys, 4);

        // update
        leaf.insert(2, 6);
        assert_eq!(leaf.keys, vec![Some(2), Some(3), Some(4), Some(8), None]);
        assert_eq!(*leaf.records[0].read(), Some(6));

        // check you can still insert when overfull
        leaf.insert(1, 10);
        assert_eq!(leaf.keys, vec![Some(1), Some(2), Some(3), Some(4), Some(8)]);
        assert_eq!(*leaf.records[0].read(), Some(10));
        assert_eq!(*leaf.records[1].read(), Some(6));
        assert_eq!(*leaf.records[2].read(), Some(8));
        assert_eq!(*leaf.records[3].read(), Some(5));
        assert_eq!(*leaf.records[4].read(), Some(9));
        assert_eq!(leaf.num_keys, 5);
    }

    #[test]
    fn test_remove() {
        let mut leaf = Leaf::<4, i32, i32>::new();
        leaf.insert(2, 2);
        leaf.remove(&2);
        assert_eq!(leaf.keys, vec![None, None, None, None]);
        assert_eq!(leaf.num_keys, 0);

        leaf.insert(2, 2);
        leaf.insert(3, 3);
        leaf.insert(4, 4);
        leaf.remove(&3);
        assert_eq!(leaf.keys, vec![Some(2), Some(4), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(2));
        assert_eq!(*leaf.records[1].read(), Some(4));
        assert_eq!(leaf.num_keys, 2);

        leaf.insert(5, 5);

        // remove non-existent keys
        leaf.remove(&-1);
        leaf.remove(&3);
        leaf.remove(&8);
        assert_eq!(leaf.num_keys, 3);

        leaf.remove(&5);
        assert_eq!(leaf.keys, vec![Some(2), Some(4), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(2));
        assert_eq!(*leaf.records[1].read(), Some(4));
        assert_eq!(leaf.num_keys, 2);

        leaf.insert(7, 7);
        leaf.remove(&2);
        assert_eq!(leaf.keys, vec![Some(4), Some(7), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(4));
        assert_eq!(*leaf.records[1].read(), Some(7));
        assert_eq!(leaf.num_keys, 2);

        leaf.remove(&4);
        assert_eq!(leaf.keys, vec![Some(7), None, None, None]);
        assert_eq!(*leaf.records[0].read(), Some(7));
        assert_eq!(leaf.num_keys, 1);
    }

    #[test]
    fn test_split_even() {
        let some_leaf = Arc::new(RwLock::new(Some(Node::Leaf(Leaf::<4, i32, i32>::new()))));

        let leaf_node = Arc::new(RwLock::new(Some(Node::Leaf(Leaf::new()))));
        let mut leaf_lock = leaf_node.write();
        let leaf = leaf_lock.as_mut().unwrap().get_leaf_mut().unwrap();
        leaf.next = Arc::downgrade(&some_leaf);
        leaf.insert(3, 3);
        leaf.insert(4, 4);
        leaf.insert(5, 5);
        leaf.insert(6, 6);

        assert_eq!(leaf.keys, vec![Some(3), Some(4), Some(5), Some(6)]);
        let (discriminator, new_leaf_node) = leaf.split(leaf_node.clone());
        let mut new_leaf_lock = new_leaf_node.write();
        let new_leaf = new_leaf_lock.as_mut().unwrap().get_leaf_mut().unwrap();

        assert_eq!(leaf.keys, vec![Some(3), Some(4), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(3));
        assert_eq!(*leaf.records[1].read(), Some(4));
        assert_eq!(leaf.num_keys, 2);
        assert!(Arc::ptr_eq(&leaf.next.upgrade().unwrap(), &new_leaf_node));

        assert_eq!(new_leaf.keys, vec![Some(5), Some(6), None, None]);
        assert_eq!(*new_leaf.records[0].read(), Some(5));
        assert_eq!(*new_leaf.records[1].read(), Some(6));
        assert_eq!(new_leaf.num_keys, 2);
        assert!(Arc::ptr_eq(&new_leaf.prev.upgrade().unwrap(), &leaf_node));
        assert!(Arc::ptr_eq(&new_leaf.next.upgrade().unwrap(), &some_leaf));

        assert_eq!(discriminator, 5);
    }

    #[test]
    fn test_split_odd() {
        let some_leaf = Arc::new(RwLock::new(Some(Node::Leaf(Leaf::<5, i32, i32>::new()))));

        let leaf_node = Arc::new(RwLock::new(Some(Node::Leaf(Leaf::new()))));
        let mut leaf_lock = leaf_node.write();
        let leaf = leaf_lock.as_mut().unwrap().get_leaf_mut().unwrap();
        leaf.next = Arc::downgrade(&some_leaf);
        leaf.insert(3, 3);
        leaf.insert(4, 4);
        leaf.insert(5, 5);
        leaf.insert(6, 6);
        leaf.insert(7, 7);

        assert_eq!(leaf.keys, vec![Some(3), Some(4), Some(5), Some(6), Some(7)]);
        let (discriminator, new_leaf_node) = leaf.split(leaf_node.clone());
        let mut new_leaf_lock = new_leaf_node.write();
        let new_leaf = new_leaf_lock.as_mut().unwrap().get_leaf_mut().unwrap();

        assert_eq!(leaf.keys, vec![Some(3), Some(4), None, None, None]);
        assert_eq!(*leaf.records[0].read(), Some(3));
        assert_eq!(*leaf.records[1].read(), Some(4));
        assert_eq!(leaf.num_keys, 2);
        assert!(Arc::ptr_eq(&leaf.next.upgrade().unwrap(), &new_leaf_node));

        assert_eq!(new_leaf.keys, vec![Some(5), Some(6), Some(7), None, None]);
        assert_eq!(*new_leaf.records[0].read(), Some(5));
        assert_eq!(*new_leaf.records[1].read(), Some(6));
        assert_eq!(*new_leaf.records[2].read(), Some(7));
        assert_eq!(new_leaf.num_keys, 3);
        assert!(Arc::ptr_eq(&new_leaf.prev.upgrade().unwrap(), &leaf_node));
        assert!(Arc::ptr_eq(&new_leaf.next.upgrade().unwrap(), &some_leaf));

        assert_eq!(discriminator, 5);
    }

    #[test]
    fn test_borrow_successor() {
        let mut successor = Leaf::<4, i32, i32>::new();
        successor.insert(3, 3);
        successor.insert(4, 4);
        successor.insert(5, 5);

        let successor_node = Arc::new(RwLock::new(Some(Node::Leaf(successor))));

        let mut leaf = Leaf::<4, i32, i32>::new();
        leaf.insert(2, 2);
        leaf.next = Arc::downgrade(&successor_node);

        let mut successor_lock = successor_node.write();
        let new_discriminator =
            leaf.borrow_from_successor(successor_lock.as_mut().unwrap().get_leaf_mut().unwrap());

        assert_eq!(new_discriminator, Some(4));

        assert_eq!(leaf.keys, vec![Some(2), Some(3), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(2));
        assert_eq!(*leaf.records[1].read(), Some(3));
        assert_eq!(leaf.num_keys, 2);

        let successor = successor_lock.as_mut().unwrap().get_leaf_mut().unwrap();
        assert_eq!(successor.keys, vec![Some(4), Some(5), None, None]);
        assert_eq!(*successor.records[0].read(), Some(4));
        assert_eq!(*successor.records[1].read(), Some(5));
        assert_eq!(successor.num_keys, 2);
    }

    #[test]
    fn test_borrow_predecessor() {
        let mut predecessor = Leaf::<4, i32, i32>::new();
        predecessor.insert(3, 3);
        predecessor.insert(4, 4);
        predecessor.insert(5, 5);

        let predecessor_node = Arc::new(RwLock::new(Some(Node::Leaf(predecessor))));

        let mut leaf = Leaf::<4, i32, i32>::new();
        leaf.insert(7, 7);
        leaf.prev = Arc::downgrade(&predecessor_node);

        let mut predecessor_lock = predecessor_node.write();
        let new_discriminator = leaf
            .borrow_from_predecessor(predecessor_lock.as_mut().unwrap().get_leaf_mut().unwrap());

        assert_eq!(new_discriminator, Some(5));

        assert_eq!(leaf.keys, vec![Some(5), Some(7), None, None]);
        assert_eq!(*leaf.records[0].read(), Some(5));
        assert_eq!(*leaf.records[1].read(), Some(7));
        assert_eq!(leaf.num_keys, 2);

        let predecessor = predecessor_lock.as_mut().unwrap().get_leaf_mut().unwrap();
        assert_eq!(predecessor.keys, vec![Some(3), Some(4), None, None]);
        assert_eq!(*predecessor.records[0].read(), Some(3));
        assert_eq!(*predecessor.records[1].read(), Some(4));
        assert_eq!(predecessor.num_keys, 2);
    }

    #[test]
    fn test_merge() {
        let mut leaf = Leaf::<6, i32, i32>::new();
        leaf.insert(1, 1);
        leaf.insert(2, 2);

        let some_leaf = Arc::new(RwLock::new(Some(Node::Leaf(Leaf::new()))));
        let mut successor = Leaf::<6, i32, i32>::new();
        successor.next = Arc::downgrade(&some_leaf);
        successor.insert(7, 7);
        successor.insert(8, 8);
        successor.insert(9, 9);

        leaf.merge(&mut successor);

        assert_eq!(
            leaf.keys,
            vec![Some(1), Some(2), Some(7), Some(8), Some(9), None]
        );

        assert_eq!(*leaf.records[0].read(), Some(1));
        assert_eq!(*leaf.records[1].read(), Some(2));
        assert_eq!(*leaf.records[2].read(), Some(7));
        assert_eq!(*leaf.records[3].read(), Some(8));
        assert_eq!(*leaf.records[4].read(), Some(9));
        assert_eq!(leaf.num_keys, 5);

        assert!(Arc::ptr_eq(&leaf.next.upgrade().unwrap(), &some_leaf));
    }
}
