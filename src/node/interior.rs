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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let interior = Interior::<4, i32, i32>::new();
        assert_eq!(interior.num_keys, 0);
        assert_eq!(interior.keys, vec![None, None, None, None]);
        assert_eq!(interior.children.len(), 5);

        for child in interior.children {
            assert!(child.read().is_none());
        }
    }

    #[test]
    fn test_insert() {
        let mut interior = Interior::<5, i32, i32>::new();
        interior.children[0] = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        interior.insert(4, child1.clone());
        assert_eq!(interior.num_keys, 1);
        assert_eq!(interior.keys, vec![Some(4), None, None, None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child1));

        // insert before 4
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        interior.insert(2, child2.clone());
        assert_eq!(interior.num_keys, 2);
        assert_eq!(interior.keys, vec![Some(2), Some(4), None, None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
        assert!(Arc::ptr_eq(&interior.children[2], &child1));

        // insert between 2 and 4
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        interior.insert(3, child3.clone());
        assert_eq!(interior.num_keys, 3);
        assert_eq!(interior.keys, vec![Some(2), Some(3), Some(4), None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
        assert!(Arc::ptr_eq(&interior.children[2], &child3));
        assert!(Arc::ptr_eq(&interior.children[3], &child1));

        // insert after 4
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        interior.insert(7, child4.clone());
        assert_eq!(interior.num_keys, 4);
        assert_eq!(
            interior.keys,
            vec![Some(2), Some(3), Some(4), Some(7), None]
        );
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
        assert!(Arc::ptr_eq(&interior.children[2], &child3));
        assert!(Arc::ptr_eq(&interior.children[3], &child1));
        assert!(Arc::ptr_eq(&interior.children[4], &child4));

        // allow inserting for overflow
        let child5 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        interior.insert(1, child5.clone());
        assert_eq!(interior.num_keys, 5);
        assert_eq!(
            interior.keys,
            vec![Some(1), Some(2), Some(3), Some(4), Some(7)]
        );
        assert!(Arc::ptr_eq(&interior.children[1], &child5));
        assert!(Arc::ptr_eq(&interior.children[2], &child2));
        assert!(Arc::ptr_eq(&interior.children[3], &child3));
        assert!(Arc::ptr_eq(&interior.children[4], &child1));
        assert!(Arc::ptr_eq(&interior.children[5], &child4));
    }

    #[test]
    fn test_remove() {
        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        let mut interior = Interior::<5, i32, i32>::new();
        interior.children[0] = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        interior.insert(2, child1.clone());

        // check underfull removal
        interior.remove(&child1);
        assert_eq!(interior.num_keys, 0);
        assert!(interior.children[1].read().is_none());

        interior.insert(2, child1.clone());
        interior.insert(4, child2.clone());
        interior.insert(7, child3.clone());
        interior.insert(10, child4.clone());

        assert_eq!(
            interior.keys,
            vec![Some(2), Some(4), Some(7), Some(10), None]
        );
        assert_eq!(interior.num_keys, 4);

        // remove from front
        interior.remove(&child1);
        assert_eq!(interior.num_keys, 3);
        assert_eq!(interior.keys, vec![Some(4), Some(7), Some(10), None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
        assert!(Arc::ptr_eq(&interior.children[2], &child3));
        assert!(Arc::ptr_eq(&interior.children[3], &child4));

        interior.remove(&child3);
        assert_eq!(interior.num_keys, 2);
        assert_eq!(interior.keys, vec![Some(4), Some(10), None, None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
        assert!(Arc::ptr_eq(&interior.children[2], &child4));

        interior.remove(&child4);
        assert_eq!(interior.num_keys, 1);
        assert_eq!(interior.keys, vec![Some(4), None, None, None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
    }

    #[test]
    fn test_split_odd() {
        let mut interior = Interior::<5, i32, i32>::new();
        interior.children[0] = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child5 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        interior.insert(3, child1.clone());
        interior.insert(5, child2.clone());
        interior.insert(9, child3.clone());
        interior.insert(16, child4.clone());
        interior.insert(22, child5.clone());

        // overfull
        assert_eq!(interior.num_keys, 5);

        let (pushed_key, new_interior) = interior.split();
        let new_interior_lock = new_interior.read();
        let new_interior = new_interior_lock.as_ref().unwrap().get_interior().unwrap();
        assert_eq!(pushed_key, 9);

        assert_eq!(interior.num_keys, 2);
        assert_eq!(interior.keys, vec![Some(3), Some(5), None, None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child1));
        assert!(Arc::ptr_eq(&interior.children[2], &child2));

        assert_eq!(new_interior.num_keys, 2);
        assert_eq!(
            new_interior.keys,
            vec![Some(16), Some(22), None, None, None]
        );
        assert!(Arc::ptr_eq(&new_interior.children[0], &child3));
        assert!(Arc::ptr_eq(&new_interior.children[1], &child4));
        assert!(Arc::ptr_eq(&new_interior.children[2], &child5));
    }

    #[test]
    fn test_split_even() {
        let mut interior = Interior::<6, i32, i32>::new();
        interior.children[0] = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child5 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child6 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        interior.insert(3, child1.clone());
        interior.insert(5, child2.clone());
        interior.insert(9, child3.clone());
        interior.insert(16, child4.clone());
        interior.insert(22, child5.clone());
        interior.insert(26, child6.clone());

        // overfull
        assert_eq!(interior.num_keys, 6);

        let (pushed_key, new_interior) = interior.split();
        let new_interior_lock = new_interior.read();
        let new_interior = new_interior_lock.as_ref().unwrap().get_interior().unwrap();
        assert_eq!(pushed_key, 9);

        assert_eq!(interior.num_keys, 2);
        assert_eq!(
            interior.keys,
            vec![Some(3), Some(5), None, None, None, None]
        );
        assert!(Arc::ptr_eq(&interior.children[1], &child1));
        assert!(Arc::ptr_eq(&interior.children[2], &child2));

        assert_eq!(new_interior.num_keys, 3);
        assert_eq!(
            new_interior.keys,
            vec![Some(16), Some(22), Some(26), None, None, None]
        );
        assert!(Arc::ptr_eq(&new_interior.children[0], &child3));
        assert!(Arc::ptr_eq(&new_interior.children[1], &child4));
        assert!(Arc::ptr_eq(&new_interior.children[2], &child5));
        assert!(Arc::ptr_eq(&new_interior.children[3], &child6));
    }

    #[test]
    fn test_borrow_successor() {
        let mut interior = Interior::<5, i32, i32>::new();
        interior.children[0] = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child5 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child6 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child7 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        interior.insert(3, child1.clone());
        interior.insert(5, child2.clone());

        let mut sibling_interior = Interior::<5, i32, i32>::new();
        sibling_interior.children[0] = child3.clone();
        sibling_interior.insert(12, child4.clone());
        sibling_interior.insert(15, child5.clone());
        sibling_interior.insert(17, child6.clone());
        sibling_interior.insert(19, child7.clone());

        let pushed_key = interior.borrow_from_successor(&mut sibling_interior, 9);
        assert_eq!(pushed_key, Some(12));

        assert_eq!(interior.num_keys, 3);
        assert_eq!(interior.keys, vec![Some(3), Some(5), Some(9), None, None]);
        assert!(Arc::ptr_eq(&interior.children[1], &child1));
        assert!(Arc::ptr_eq(&interior.children[2], &child2));
        assert!(Arc::ptr_eq(&interior.children[3], &child3));

        assert_eq!(sibling_interior.num_keys, 3);
        assert_eq!(
            sibling_interior.keys,
            vec![Some(15), Some(17), Some(19), None, None]
        );
        assert!(Arc::ptr_eq(&sibling_interior.children[0], &child4));
        assert!(Arc::ptr_eq(&sibling_interior.children[1], &child5));
        assert!(Arc::ptr_eq(&sibling_interior.children[2], &child6));
        assert!(Arc::ptr_eq(&sibling_interior.children[3], &child7));
    }

    #[test]
    fn test_borrow_predecessor() {
        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child5 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child6 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child7 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        let mut interior = Interior::<5, i32, i32>::new();
        interior.children[0] = child1.clone();
        interior.insert(15, child2.clone());
        interior.insert(18, child3.clone());

        let mut sibling_interior = Interior::<5, i32, i32>::new();
        sibling_interior.children[0] = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        sibling_interior.insert(2, child4.clone());
        sibling_interior.insert(5, child5.clone());
        sibling_interior.insert(7, child6.clone());
        sibling_interior.insert(12, child7.clone());

        let pushed_key = interior.borrow_from_predecessor(&mut sibling_interior, 14);
        assert_eq!(pushed_key, Some(12));

        assert_eq!(interior.num_keys, 3);
        assert_eq!(
            interior.keys,
            vec![Some(14), Some(15), Some(18), None, None]
        );
        assert!(Arc::ptr_eq(&interior.children[0], &child7));
        assert!(Arc::ptr_eq(&interior.children[1], &child1));
        assert!(Arc::ptr_eq(&interior.children[2], &child2));
        assert!(Arc::ptr_eq(&interior.children[3], &child3));

        assert_eq!(sibling_interior.num_keys, 3);
        assert_eq!(
            sibling_interior.keys,
            vec![Some(2), Some(5), Some(7), None, None]
        );
        assert!(Arc::ptr_eq(&sibling_interior.children[1], &child4));
        assert!(Arc::ptr_eq(&sibling_interior.children[2], &child5));
        assert!(Arc::ptr_eq(&sibling_interior.children[3], &child6));
    }

    #[test]
    fn test_merge() {
        let child1 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child2 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child3 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child4 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));
        let child5 = Arc::new(RwLock::new(Some(Node::Leaf(Node::new_leaf()))));

        let mut interior = Interior::<5, i32, i32>::new();
        interior.children[0] = child1.clone();
        interior.insert(2, child2.clone());

        let mut sibling_interior = Interior::<5, i32, i32>::new();
        sibling_interior.children[0] = child3.clone();
        sibling_interior.insert(12, child4.clone());
        sibling_interior.insert(15, child5.clone());

        interior.merge(&mut sibling_interior, 9);
        assert_eq!(interior.num_keys, 4);
        assert_eq!(
            interior.keys,
            vec![Some(2), Some(9), Some(12), Some(15), None]
        );
        assert!(Arc::ptr_eq(&interior.children[0], &child1));
        assert!(Arc::ptr_eq(&interior.children[1], &child2));
        assert!(Arc::ptr_eq(&interior.children[2], &child3));
        assert!(Arc::ptr_eq(&interior.children[3], &child4));
        assert!(Arc::ptr_eq(&interior.children[4], &child5));
    }
}
