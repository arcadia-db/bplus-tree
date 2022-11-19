use super::{node::*, typedefs::*};
use std::mem;
use std::sync::{Arc, RwLock};

#[derive(Debug)]
pub struct BPTree<const FANOUT: usize, K: Key, V: Record> {
    root: Option<NodePtr<FANOUT, K, V>>,
}

impl<const FANOUT: usize, K: Key, V: Record> BPTree<FANOUT, K, V> {
    pub fn new() -> Self {
        assert!(FANOUT > 1);
        Self { root: None }
    }

    pub fn search(&self, key: &K) -> Option<RecordPtr<V>> {
        let leaf = self.get_leaf_node(key)?;
        let lock = leaf.read().unwrap();
        let leaf = lock.get_leaf()?;
        for i in 0..leaf.num_keys {
            if *key == *leaf.keys[i].as_ref()? {
                return Some(leaf.records[i].as_ref()?.clone());
            }
        }
        // println!("{:#?}", leaf.parent.as_ref()?.upgrade());
        None
    }

    pub fn search_range(&self, (start, end): (&K, &K)) -> Vec<RecordPtr<V>> {
        assert!(end >= start);

        let mut result: Vec<RecordPtr<V>> = Vec::new();

        let mut leaf = self.get_leaf_node(start);
        // the only case the leaf is none is if the root node is None (empty tree)
        if leaf.is_none() {
            return result;
        }

        // Find position within leaf
        let leaf_lock = leaf.as_ref().unwrap().read().unwrap();
        let leaf_node = leaf_lock.get_leaf().unwrap();

        let mut i = 0;
        while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() < start {
            i += 1;
        }
        drop(leaf_lock);

        while leaf.is_some() {
            let leaf_lock = leaf.as_ref().unwrap().read().unwrap();
            let leaf_node = leaf_lock.get_leaf().unwrap();

            while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() <= end {
                if leaf_node.keys[i].as_ref().unwrap() >= start {
                    result.push(leaf_node.records[i].as_ref().unwrap().clone());
                }
                i += 1;
            }
            if i != leaf_node.num_keys {
                drop(leaf_lock);
                break;
            }

            let next = leaf_node.next.clone();
            drop(leaf_lock);
            if next.is_none() {
                break;
            }
            leaf = next.unwrap().upgrade();
            i = 0;
        }

        result
    }

    pub fn insert(&mut self, key: K, record: V) {
        // There are 3 cases for insert

        // 1 - key exists so just update the record
        let searched_record = self.search(&key);
        if let Some(value) = searched_record {
            let mut lock = value.write().unwrap();
            *lock = record;
            drop(lock);
            return;
        }

        // 2 - Empty tree so start a new tree
        if self.root.is_none() {
            let mut new_node = Node::new_leaf();
            new_node.keys[0] = Some(key);
            new_node.records[0] = Some(Arc::new(RwLock::new(record)));
            new_node.num_keys += 1;
            self.root = Some(Arc::new(RwLock::new(Node::Leaf(new_node))));
            return;
        }

        let leaf_node = self.get_leaf_node(&key).unwrap();
        let mut leaf_lock = leaf_node.write().unwrap();

        // 3 - Insert into leaf, splitting if needed
        let leaf = leaf_lock.get_leaf_mut().unwrap();

        let mut insertion_idx = 0;
        while insertion_idx < leaf.num_keys && *leaf.keys[insertion_idx].as_ref().unwrap() < key {
            insertion_idx += 1
        }

        let mut i = leaf.num_keys;
        while i > insertion_idx {
            leaf.keys.swap(i, i - 1);
            leaf.records.swap(i, i - 1);
            i -= 1
        }
        leaf.keys[insertion_idx] = Some(key);
        leaf.records[insertion_idx] = Some(Arc::new(RwLock::new(record)));
        leaf.num_keys += 1;

        // split if overflow (this is why we added 1 extra spot in the array)
        if leaf.num_keys == FANOUT {
            let mut new_leaf: Leaf<FANOUT, K, V> = Node::new_leaf();
            let split = FANOUT / 2;

            for i in split..leaf.num_keys {
                mem::swap(&mut new_leaf.keys[i - split], &mut leaf.keys[i]);
                mem::swap(&mut new_leaf.records[i - split], &mut leaf.records[i]);
            }

            new_leaf.num_keys = leaf.num_keys - split;
            new_leaf.parent = leaf.parent.clone();
            leaf.num_keys = split;

            let new_key = new_leaf.keys[0].clone().unwrap();
            new_leaf.prev = Some(Arc::downgrade(&leaf_node));
            new_leaf.next = leaf.next.clone();

            let new_leaf_node = Arc::new(RwLock::new(Node::Leaf(new_leaf)));
            leaf.next = Some(Arc::downgrade(&new_leaf_node));
            drop(leaf_lock);

            self.insert_into_parent(leaf_node, new_key, new_leaf_node);
        }
    }

    pub fn remove(&mut self, key: &K) {
        let leaf = self.get_leaf_node(key);
        if leaf.is_none() {
            return;
        }
        let leaf_node = leaf.as_ref().unwrap();
        let mut leaf_lock = leaf_node.as_ref().write().ok().unwrap();
        let leaf = leaf_lock.get_leaf_mut().unwrap();
        let mut i = 0;
        while i < leaf.num_keys && leaf.keys[i].as_ref().unwrap() != key {
            i += 1;
        }
        if i == leaf.num_keys {
            return;
        }

        leaf.keys[i] = None;
        leaf.records[i] = None;
        for j in i..leaf.num_keys - 1 {
            leaf.keys.swap(j, j + 1);
            leaf.records.swap(j, j + 1);
        }
        leaf.num_keys -= 1;

        // leaf is the root node
        if leaf.parent.is_none() {
            if leaf.num_keys == 0 {
                self.root = None;
            }
            return;
        }

        if leaf.num_keys >= (FANOUT - 1) / 2 {
            return;
        }

        let parent_node = leaf.parent.as_ref().unwrap().upgrade().unwrap();
        let mut parent_lock = parent_node.write().ok().unwrap();
        let parent = parent_lock.get_interior_mut().unwrap();
        if parent.num_keys == 0 {
            println!("{:#?}", parent);
        }
        debug_assert!(parent.num_keys > 0);
        let mut i = 0;
        while i <= parent.num_keys && !Arc::ptr_eq(&leaf_node, parent.children[i].as_ref().unwrap())
        {
            i += 1;
        }
        // we have too few keys in the node
        let (discriminator_key, sibling_node) = if i < parent.num_keys {
            (
                parent.keys[i].clone().unwrap(),
                parent.children[i + 1].as_ref().unwrap(),
            )
        } else {
            (
                parent.keys[i - 1].clone().unwrap(),
                parent.children[i - 1].as_ref().unwrap(),
            )
        };

        // we have too few keys in the node
        let mut sibling_lock = sibling_node.write().ok().unwrap();
        let sibling = sibling_lock.get_leaf_mut().unwrap();
        let (first, second) = if i < parent.num_keys {
            (leaf, sibling)
        } else {
            (sibling, leaf)
        };

        // keys can fit into one node so let's merge
        if first.num_keys + second.num_keys <= FANOUT - 1 {
            for i in 0..second.num_keys {
                mem::swap(&mut first.keys[i + first.num_keys], &mut second.keys[i]);
                mem::swap(
                    &mut first.records[i + first.num_keys],
                    &mut second.records[i],
                );
            }
            first.num_keys = first.num_keys + second.num_keys;
            first.next = second.next.clone();
            second.prev = None;

            let right_child = if i < parent.num_keys {
                sibling_node.clone()
            } else {
                leaf_node.clone()
            };
            drop(leaf_lock);
            drop(sibling_lock);
            drop(parent_lock);
            self.remove_from_parent(parent_node, &right_child);
        }
        // otherwise, we can borrow one from the other node
        else {
            // borrow from second
            if first.num_keys < second.num_keys {
                mem::swap(&mut first.keys[first.num_keys], &mut second.keys[0]);
                mem::swap(&mut first.records[first.num_keys], &mut second.records[0]);
                for i in 1..second.num_keys {
                    second.keys.swap(i - 1, i);
                    second.records.swap(i - 1, i);
                }
                first.num_keys += 1;
                second.num_keys -= 1;
            }
            // borrow from first
            else {
                let mut i = second.num_keys;
                while i > 0 {
                    second.keys.swap(i, i - 1);
                    second.records.swap(i, i - 1);
                    i -= 1;
                }
                mem::swap(&mut second.keys[0], &mut first.keys[first.num_keys - 1]);
                mem::swap(
                    &mut second.records[0],
                    &mut first.records[first.num_keys - 1],
                );
                first.num_keys -= 1;
                second.num_keys += 1;
            };

            // replace the key in parent
            for parent_key in &mut parent.keys {
                if *parent_key.as_ref().unwrap() == discriminator_key {
                    parent_key.replace(second.keys[0].clone().unwrap());
                    break;
                }
            }
        }
    }

    /* private */
    fn insert_into_parent(
        &mut self,
        left: NodePtr<FANOUT, K, V>,
        key: K,
        right: NodePtr<FANOUT, K, V>,
    ) {
        let left_lock = left.read().unwrap();
        let parent = left_lock.get_parent();
        drop(left_lock);

        // 2 cases for insert into parent
        // 1 - No parent for left/right. We need to make a new root node if there is no parent
        if parent.is_none() {
            let mut new_node: Interior<FANOUT, K, V> = Node::new_interior();
            new_node.keys[0] = Some(key);
            new_node.children[0] = Some(left.clone());
            new_node.children[1] = Some(right.clone());
            new_node.num_keys = 1;
            self.root = Some(Arc::new(RwLock::new(Node::Interior(new_node))));

            let mut left_lock = left.write().unwrap();
            left_lock.set_parent(Some(self.root.as_ref().unwrap().clone()));
            drop(left_lock);

            let mut right_lock = right.write().unwrap();
            right_lock.set_parent(Some(self.root.as_ref().unwrap().clone()));
            drop(right_lock);
            return;
        }
        let parent_node = parent.unwrap().upgrade().unwrap();
        let mut parent_lock = parent_node.write().unwrap();
        let parent = parent_lock.get_interior_mut().unwrap();

        // assign right's parent pointer
        let mut right_lock = right.write().unwrap();
        right_lock.set_parent(Some(parent_node.clone()));
        drop(right_lock);

        let mut left_idx_in_parent = 0;
        while left_idx_in_parent < parent.num_keys
            && !Arc::ptr_eq(parent.children[left_idx_in_parent].as_ref().unwrap(), &left)
        {
            left_idx_in_parent += 1
        }

        let mut i = parent.num_keys + 1;
        while i > left_idx_in_parent + 1 {
            parent.keys.swap(i - 1, i - 2);
            parent.children.swap(i, i - 1);
            i -= 1
        }
        parent.keys[left_idx_in_parent] = Some(key);
        parent.children[left_idx_in_parent + 1] = Some(right.clone());
        parent.num_keys += 1;

        // 2 - interior node has no space so we have to split it
        if parent.num_keys == FANOUT {
            let mut new_interior: Interior<FANOUT, K, V> = Node::new_interior();
            let split = (FANOUT + 1) / 2 - 1;

            for i in split + 1..parent.num_keys {
                mem::swap(&mut parent.keys[i], &mut new_interior.keys[i - split - 1]);
                mem::swap(
                    &mut parent.children[i],
                    &mut new_interior.children[i - split - 1],
                );
            }
            let pushed_key = parent.keys[split].as_ref().unwrap().clone();
            mem::swap(
                &mut parent.children[FANOUT],
                &mut new_interior.children[parent.num_keys - split - 1],
            );
            parent.keys[split] = None;

            new_interior.num_keys = parent.num_keys - split - 1;
            parent.num_keys = split;
            new_interior.parent = parent.parent.clone();
            let new_interior_node = Arc::new(RwLock::new(Node::Interior(new_interior)));
            let new_interior_lock = new_interior_node.read().unwrap();
            let new_interior = new_interior_lock.get_interior().unwrap();

            for i in 0..new_interior.num_keys + 1 {
                let child = new_interior.children[i].as_ref().unwrap();
                let mut child_lock = child.write().unwrap();
                child_lock.set_parent(Some(new_interior_node.clone()));
                drop(child_lock);
            }
            drop(new_interior_lock);
            drop(parent_lock);
            self.insert_into_parent(parent_node, pushed_key, new_interior_node);
        }
    }

    fn remove_from_parent(
        &mut self,
        node: NodePtr<FANOUT, K, V>,
        right_child: &NodePtr<FANOUT, K, V>,
    ) {
        let mut interior_lock = node.write().ok().unwrap();
        let mut interior = interior_lock.get_interior_mut().unwrap();
        let mut right_child_idx = 0;
        while right_child_idx <= interior.num_keys
            && !Arc::ptr_eq(
                &interior.children[right_child_idx].as_ref().unwrap(),
                right_child,
            )
        {
            right_child_idx += 1;
        }
        debug_assert_ne!(right_child_idx, interior.num_keys + 1);

        interior.keys[right_child_idx - 1] = None;
        interior.children[right_child_idx] = None;
        for j in right_child_idx - 1..interior.num_keys - 1 {
            interior.keys.swap(j, j + 1);
            interior.children.swap(j + 1, j + 2);
        }
        interior.num_keys -= 1;

        // interior is the root node
        if interior.parent.is_none() {
            if interior.num_keys == 0 {
                self.root = interior.children[0].clone();
                drop(interior_lock);
                let mut root_lock = self.root.as_ref().unwrap().write().ok().unwrap();
                root_lock.set_parent(None);
            }
            return;
        }

        if interior.num_keys >= FANOUT / 2 {
            return;
        }

        let parent_node = interior.parent.as_ref().unwrap().upgrade().unwrap();
        let mut parent_lock = parent_node.write().ok().unwrap();
        let parent = parent_lock.get_interior_mut().unwrap();

        let mut i = 0;
        while i <= parent.num_keys && !Arc::ptr_eq(&node, parent.children[i].as_ref().unwrap()) {
            i += 1;
        }
        // we have too few keys in the node
        let (discriminator_key_2, sibling_node) = if i < parent.num_keys {
            (
                parent.keys[i].clone().unwrap(),
                parent.children[i + 1].as_ref().unwrap(),
            )
        } else {
            (
                parent.keys[i - 1].clone().unwrap(),
                parent.children[i - 1].as_ref().unwrap(),
            )
        };
        let mut sibling_lock = sibling_node.write().ok().unwrap();
        let sibling = sibling_lock.get_interior_mut().unwrap();
        let (first, second) = if i < parent.num_keys {
            (interior, sibling)
        } else {
            (sibling, interior)
        };

        // we can borrow a key from one the other node
        if first.num_keys >= (FANOUT + 1) / 2 || second.num_keys >= (FANOUT + 1) / 2 {
            let replacement_key;
            // borrow from second (the interior node in question is predecessor)
            if first.num_keys < second.num_keys {
                first.keys[first.num_keys] = Some(discriminator_key_2.clone());
                mem::swap(
                    &mut first.children[first.num_keys + 1],
                    &mut second.children[0],
                );

                let child = first.children[first.num_keys + 1].as_ref().unwrap();
                let mut child_lock = child.write().ok().unwrap();
                child_lock.set_parent(Some(node.clone()));
                drop(child_lock);

                replacement_key = second.keys[0].clone();
                second.keys[0] = None;
                for i in 1..second.num_keys {
                    second.keys.swap(i - 1, i);
                    second.children.swap(i - 1, i);
                }
                second.children.swap(second.num_keys - 1, second.num_keys);
                first.num_keys += 1;
                second.num_keys -= 1;
                debug_assert!(first.num_keys > 0);
                debug_assert!(second.num_keys > 0);
            }
            // borrow from first (the interior node in question is the successor)
            else {
                let mut i = second.num_keys;
                second.children.swap(second.num_keys + 1, second.num_keys);
                while i > 0 {
                    second.keys.swap(i, i - 1);
                    second.children.swap(i, i - 1);
                    i -= 1;
                }
                replacement_key = first.keys[first.num_keys - 1].clone();
                first.keys[first.num_keys - 1] = None;
                second.keys[0] = Some(discriminator_key_2.clone());
                mem::swap(&mut second.children[0], &mut first.children[first.num_keys]);
                let child = second.children[0].as_ref().unwrap();
                let mut child_lock = child.write().ok().unwrap();
                child_lock.set_parent(Some(node.clone()));
                drop(child_lock);

                first.num_keys -= 1;
                second.num_keys += 1;
                debug_assert!(first.num_keys > 0);
                debug_assert!(second.num_keys > 0);
            };

            // replace the key in parent
            for parent_key in &mut parent.keys {
                if *parent_key.as_ref().unwrap() == discriminator_key_2 {
                    parent_key.replace(replacement_key.clone().unwrap());
                    break;
                }
            }
        }
        // keys can fit into one node so let's merge
        else {
            first.keys[first.num_keys] = Some(discriminator_key_2.clone());
            for j in 0..second.num_keys {
                mem::swap(&mut first.keys[j + first.num_keys + 1], &mut second.keys[j]);
            }
            for j in 0..second.num_keys + 1 {
                mem::swap(
                    &mut first.children[j + first.num_keys + 1],
                    &mut second.children[j],
                );
                let child_node = first.children[j + first.num_keys + 1].as_ref().unwrap();
                let mut child_lock = child_node.write().ok().unwrap();

                if i < parent.num_keys {
                    child_lock.set_parent(Some(node.clone()));
                } else {
                    child_lock.set_parent(Some(sibling_node.clone()));
                }
                drop(child_lock);
            }

            let right_child = if i < parent.num_keys {
                sibling_node.clone()
            } else {
                node.clone()
            };
            first.num_keys = first.num_keys + second.num_keys + 1;
            debug_assert!(first.num_keys > 0);
            drop(sibling_lock);
            drop(interior_lock);
            drop(parent_lock);
            self.remove_from_parent(parent_node, &right_child);
        }
    }

    /* private */
    fn get_leaf_node(&self, key: &K) -> Option<NodePtr<FANOUT, K, V>> {
        let mut current = self.root.clone()?;
        loop {
            let lock = current.read().unwrap();
            if lock.get_interior().is_none() {
                break;
            }

            let next = {
                let mut i = 0;
                let node = lock.get_interior().unwrap();
                while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
                    i += 1;
                }
                node.children[i].as_ref().unwrap().clone()
            };

            drop(lock);
            current = next;
        }

        Some(current)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, RwLock};

    impl Key for i32 {}
    impl Key for usize {}

    impl Record for i32 {}
    impl Record for usize {}

    impl Record for String {}

    #[test]
    fn test_search() {
        const TEST_FANOUT: usize = 2;
        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(0), Some(2)],
            records: vec![
                Some(Arc::new(RwLock::new(String::from("John")))),
                Some(Arc::new(RwLock::new(String::from("Adam")))),
            ],
            parent: None,
            prev: None,
            next: None,
        });
        let node_leaf1_ptr = Arc::new(RwLock::new(node_leaf1));

        // Create node (10 = "Emily"), (12 = "Jessica")
        let node_leaf2: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(10), Some(12)],
            records: vec![
                Some(Arc::new(RwLock::new(String::from("Emily")))),
                Some(Arc::new(RwLock::new(String::from("Jessica")))),
            ],
            parent: None,
            prev: Some(Arc::downgrade(&node_leaf1_ptr)),
            next: None,
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(node_leaf2));

        // Create node (20 = "Sam")
        let node_leaf3: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 1,
            keys: vec![Some(20), None],
            records: vec![Some(Arc::new(RwLock::new(String::from("Sam")))), None],
            parent: None,
            prev: Some(Arc::downgrade(&node_leaf2_ptr)),
            next: None,
        });
        let node_leaf3_ptr = Arc::new(RwLock::new(node_leaf3));

        // Set node_leaf1_ptr's ptr_leaf_next to node_leaf2_ptr
        let mut lock = node_leaf1_ptr.write().unwrap();
        lock.get_leaf_mut().unwrap().next = Some(Arc::downgrade(&node_leaf2_ptr));
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write().unwrap();
        lock.get_leaf_mut().unwrap().next = Some(Arc::downgrade(&node_leaf3_ptr));
        drop(lock);

        // Create interior (node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr)
        let node_interior1: Node<TEST_FANOUT, i32, String> = Node::Interior(Interior {
            num_keys: 2,
            keys: vec![Some(10), Some(20)],
            children: vec![
                Some(node_leaf1_ptr),
                Some(node_leaf2_ptr),
                Some(node_leaf3_ptr),
            ],
            parent: None,
        });
        let node_interior1_ptr = Arc::new(RwLock::new(node_interior1));

        // Set all children of node_interior1's ptr_leaf_parent to node_interior1
        let mut lock = node_interior1_ptr.write().unwrap();
        for child in &lock.get_interior_mut().unwrap().children {
            if let Some(ptr) = child.as_ref() {
                let mut ptr_lock = ptr.write().unwrap();
                ptr_lock.get_leaf_mut().unwrap().parent = Some(Arc::downgrade(&node_interior1_ptr));
                drop(ptr_lock);
            }
        }
        drop(lock);

        // Create B+Tree
        let bptree1: BPTree<TEST_FANOUT, i32, String> = BPTree {
            root: Some(node_interior1_ptr),
        };

        let res = bptree1.search(&0).unwrap();
        let lock = res.read().ok().unwrap();
        assert_eq!(*lock, "John");
        drop(lock);

        let res = bptree1.search(&2).unwrap();
        let lock = res.read().ok().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search(&10).unwrap();
        let lock = res.read().ok().unwrap();
        assert_eq!(*lock, "Emily");
        drop(lock);

        let res = bptree1.search(&12).unwrap();
        let lock = res.read().ok().unwrap();
        assert_eq!(*lock, "Jessica");
        drop(lock);

        let res = bptree1.search(&20).unwrap();
        let lock = res.read().ok().unwrap();
        assert_eq!(*lock, "Sam");
        drop(lock);

        let res = bptree1.search(&-4);
        assert!(res.is_none());

        let res = bptree1.search(&3);
        assert!(res.is_none());

        let res = bptree1.search(&14);
        assert!(res.is_none());

        let res = bptree1.search(&21);
        assert!(res.is_none());
    }

    #[test]
    fn test_range_search() {
        const TEST_FANOUT: usize = 2;

        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(0), Some(2)],
            records: vec![
                Some(Arc::new(RwLock::new(String::from("John")))),
                Some(Arc::new(RwLock::new(String::from("Adam")))),
            ],
            parent: None,
            prev: None,
            next: None,
        });
        let node_leaf1_ptr = Arc::new(RwLock::new(node_leaf1));

        // Create node (10 = "Emily"), (12 = "Jessica")
        let node_leaf2: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(10), Some(12)],
            records: vec![
                Some(Arc::new(RwLock::new(String::from("Emily")))),
                Some(Arc::new(RwLock::new(String::from("Jessica")))),
            ],
            parent: None,
            prev: Some(Arc::downgrade(&node_leaf1_ptr)),
            next: None,
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(node_leaf2));

        // Create node (20 = "Sam")
        let node_leaf3: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 1,
            keys: vec![Some(20), None],
            records: vec![Some(Arc::new(RwLock::new(String::from("Sam")))), None],
            parent: None,
            prev: Some(Arc::downgrade(&node_leaf2_ptr)),
            next: None,
        });
        let node_leaf3_ptr = Arc::new(RwLock::new(node_leaf3));

        // Set node_leaf1_ptr's ptr_leaf_next to node_leaf2_ptr
        let mut lock = node_leaf1_ptr.write().unwrap();
        lock.get_leaf_mut().unwrap().next = Some(Arc::downgrade(&node_leaf2_ptr));
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write().unwrap();
        lock.get_leaf_mut().unwrap().next = Some(Arc::downgrade(&node_leaf3_ptr));
        drop(lock);

        // Create interior (node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr)
        let node_interior1: Node<TEST_FANOUT, i32, String> = Node::Interior(Interior {
            num_keys: 2,
            keys: vec![Some(10), Some(20)],
            children: vec![
                Some(node_leaf1_ptr),
                Some(node_leaf2_ptr),
                Some(node_leaf3_ptr),
            ],
            parent: None,
        });
        let node_interior1_ptr = Arc::new(RwLock::new(node_interior1));

        // Set all children of node_interior1's ptr_leaf_parent to node_interior1
        let mut lock = node_interior1_ptr.write().unwrap();
        for child in &lock.get_interior_mut().unwrap().children {
            if let Some(ptr) = child.as_ref() {
                let mut ptr_lock = ptr.write().unwrap();
                ptr_lock.get_leaf_mut().unwrap().parent = Some(Arc::downgrade(&node_interior1_ptr));
                drop(ptr_lock);
            }
        }
        drop(lock);

        // Create B+Tree
        let bptree1: BPTree<TEST_FANOUT, i32, String> = BPTree {
            root: Some(node_interior1_ptr),
        };

        let res = bptree1.search_range((&1, &2));
        let lock = res[0].read().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range((&0, &2));
        let lock = res[0].read().unwrap();
        assert_eq!(*lock, "John");
        drop(lock);
        let lock = res[1].read().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range((&2, &12));
        let lock = res[0].read().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);
        let lock = res[1].read().unwrap();
        assert_eq!(*lock, "Emily");
        drop(lock);
        let lock = res[2].read().unwrap();
        assert_eq!(*lock, "Jessica");
        drop(lock);
    }

    #[test]
    fn test_range_search_2() {
        let mut bptree: BPTree<3, i32, String> = BPTree::new();
        bptree.insert(3, String::from("a"));
        bptree.insert(5, String::from("b"));
        bptree.insert(1, String::from("c"));

        assert_eq!(
            bptree
                .search_range((&2, &7))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<String>>(),
            vec![String::from("a"), String::from("b")],
        );

        bptree.insert(4, String::from("d"));
        assert_eq!(
            bptree
                .search_range((&2, &7))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<String>>(),
            vec![String::from("a"), String::from("d"), String::from("b")],
        );

        let mut bptree: BPTree<3, i32, i32> = BPTree::new();
        bptree.insert(1, 1);
        bptree.insert(2, 2);
        bptree.insert(4, 4);
        bptree.insert(9, 9);
        bptree.insert(15, 15);
        bptree.insert(18, 18);
        bptree.insert(19, 19);
        bptree.insert(21, 21);
        bptree.insert(34, 34);
        bptree.insert(121, 121);

        // search with both bounds in tree
        assert_eq!(
            bptree
                .search_range((&2, &18))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![2, 4, 9, 15, 18],
        );

        assert_eq!(
            bptree
                .search_range((&18, &34))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18, 19, 21, 34],
        );

        assert_eq!(
            bptree
                .search_range((&18, &18))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18],
        );

        // search with start in tree and end not in tree
        assert_eq!(
            bptree
                .search_range((&2, &24))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![2, 4, 9, 15, 18, 19, 21],
        );

        assert_eq!(
            bptree
                .search_range((&18, &20))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18, 19],
        );

        // search with start not in tree but end in tree
        assert_eq!(
            bptree
                .search_range((&5, &18))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![9, 15, 18],
        );

        assert_eq!(
            bptree
                .search_range((&0, &9))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![1, 2, 4, 9],
        );

        assert_eq!(
            bptree
                .search_range((&14, &34))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![15, 18, 19, 21, 34],
        );

        assert_eq!(
            bptree
                .search_range((&16, &21))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18, 19, 21],
        );

        assert_eq!(
            bptree
                .search_range((&3, &15))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![4, 9, 15],
        );

        // search with both bounds not in tree
        assert_eq!(
            bptree
                .search_range((&16, &22))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18, 19, 21],
        );

        assert_eq!(
            bptree
                .search_range((&35, &123))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![121],
        );

        assert_eq!(
            bptree
                .search_range((&3, &17))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![4, 9, 15],
        );

        assert_eq!(
            bptree
                .search_range((&20, &35))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![21, 34],
        );

        // search outside the range of the interval (empty)
        assert_eq!(
            bptree
                .search_range((&-5, &0))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![],
        );

        assert_eq!(
            bptree
                .search_range((&122, &156))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![],
        );
    }

    #[test]
    fn test_range_search_3() {
        let mut bptree: BPTree<3, i32, String> = BPTree::new();
        bptree.insert(3, "John".into());
        bptree.insert(6, "Emily".into());
        bptree.insert(9, "Sam".into());

        assert_eq!(
            bptree
                .search_range((&5, &10))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<String>>(),
            vec![String::from("Emily"), String::from("Sam")],
        );
    }

    #[test]
    fn test_insert() {
        let mut bptree: BPTree<3, i32, String> = BPTree::new();
        bptree.insert(3, String::from("Emily"));
        bptree.insert(5, String::from("Srihari"));

        let res = bptree.search(&3).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Emily");
        drop(lock);

        let res = bptree.search(&5).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Srihari");
        drop(lock);

        // update value of 5
        bptree.insert(5, String::from("Cool"));
        let res = bptree.search(&5).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Cool");
        drop(lock);

        // this should trigger a leaf split, and create a new root node
        bptree.insert(7, String::from("Rajat"));
        let res = bptree.search(&7).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Rajat");
        drop(lock);

        bptree.insert(4, String::from("Erik"));
        let res = bptree.search(&4).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Erik");
        drop(lock);

        // This causes a new leaf node and adding a key to the root internal node
        // println!("{:#?}", bptree);
        bptree.insert(14, String::from("Golden"));
        let res = bptree.search(&14).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Golden");
        drop(lock);

        bptree.insert(16, String::from("Backpack"));
        let res = bptree.search(&16).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Backpack");
        drop(lock);
    }

    #[test]
    fn test_insert_sequential() {
        let mut bptree: BPTree<3, i32, String> = BPTree::new();
        bptree.insert(0, String::from("Srihari"));
        bptree.insert(1, String::from("Vishnu"));
        bptree.insert(2, String::from("Rajat"));
        bptree.insert(3, String::from("Patwari"));
        bptree.insert(4, String::from("Golden"));

        let res = bptree.search(&4).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Golden");
        drop(lock);

        let res = bptree.search_range((&1, &4));

        let expected = ["Vishnu", "Rajat", "Patwari", "Golden"];

        for i in 0..res.len() {
            let lock = res[i].read().unwrap();
            assert_eq!(expected[i], *lock);
            drop(lock);
        }
        // println!("{:#?}", bptree);
    }

    #[test]
    fn test_insert_large() {
        let keys = vec![
            4, 56, 81, 71, 57, 62, 12, 91, 31, 58, 92, 37, 61, 11, 98, 75, 17, 35, 36, 23, 39, 95,
            42, 78, 38, 13, 30, 34, 84, 69, 54, 50, 99, 43, 2, 83, 28, 27, 19, 45, 32, 80, 3, 47,
            90, 14, 49, 67, 72, 25, 24, 52, 93, 51, 0, 44, 18, 86, 66, 10, 88, 6, 79, 48, 68, 26,
            33, 21, 60, 73, 41, 29, 87, 89, 97, 40, 94, 8, 20, 15, 1, 74, 59, 70, 96, 16, 22, 77,
            53, 82, 85, 7, 5, 55, 63, 46, 76, 64, 65, 9,
        ];

        let values = vec![
            99, 27, 34, 37, 23, 38, 47, 67, 45, 17, 3, 50, 5, 70, 3, 53, 26, 36, 69, 68, 56, 77,
            49, 37, 11, 16, 6, 16, 86, 30, 77, 3, 12, 31, 35, 76, 79, 9, 91, 47, 79, 91, 62, 91,
            61, 80, 29, 89, 89, 46, 18, 86, 26, 14, 98, 87, 92, 74, 4, 26, 29, 17, 76, 70, 10, 1,
            75, 50, 20, 50, 47, 15, 44, 30, 78, 3, 69, 22, 60, 88, 48, 32, 32, 73, 73, 16, 85, 50,
            8, 24, 41, 87, 78, 75, 60, 66, 5, 70, 94, 97,
        ];

        let expected = vec![
            98, 48, 35, 62, 99, 78, 17, 87, 22, 97, 26, 70, 47, 16, 80, 88, 16, 26, 92, 91, 60, 50,
            85, 68, 18, 46, 1, 9, 79, 15, 6, 45, 79, 75, 16, 36, 69, 50, 11, 56, 3, 47, 49, 31, 87,
            47, 66, 91, 70, 29, 3, 14, 86, 8, 77, 75, 27, 23, 17, 32, 20, 5, 38, 60, 70, 94, 4, 89,
            10, 30, 73, 37, 89, 50, 32, 53, 5, 50, 37, 76, 91, 34, 24, 76, 86, 41, 74, 44, 29, 30,
            61, 67, 3, 26, 69, 77, 73, 78, 3, 12,
        ];

        sizes_insert_helper(&keys, &values, &expected, true);
    }

    #[test]
    fn test_insert_small() {
        let keys: Vec<usize> = vec![9, 7, 1, 7, 4, 5, 5, 2, 1, 9];
        let values: Vec<usize> = vec![89, 3, 54, 90, 19, 2, 44, 85, 94, 10];
        let expected: Vec<usize> = vec![94, 85, 19, 44, 90, 10];

        // since there are repeated keys, keep the verify as false
        sizes_insert_helper(&keys, &values, &expected, false);
    }

    #[test]
    fn test_remove_simple() {
        let mut bptree: BPTree<3, i32, i32> = BPTree::new();

        // root is leaf and remove remaining key results in empty tree
        bptree.insert(4, 4);
        bptree.remove(&4);
        assert!(bptree.root.is_none());

        bptree.insert(5, 5);
        bptree.insert(4, 4);
        bptree.remove(&4);
        assert!(bptree.search(&4).is_none());
        bptree.search(&5).safe_read(|val| assert_eq!(*val, 5));

        // root is full
        bptree.insert(4, 4);

        // trigger split
        bptree.insert(6, 6);
        bptree
            .root
            .safe_read(|node| assert_eq!(node.get_interior().unwrap().num_keys, 1));
        bptree.remove(&6);
        assert!(bptree.search(&6).is_none());
        bptree.remove(&5);
        bptree
            .root
            .safe_read(|node| assert_eq!(node.get_leaf().unwrap().num_keys, 1));
    }

    #[test]
    fn test_remove() {
        let mut bptree: BPTree<3, i32, i32> = BPTree::new();
        bptree.insert(1, 1);
        bptree.insert(2, 2);
        bptree.insert(5, 5);
        bptree.insert(3, 3);
        bptree.insert(4, 4);
        bptree.insert(8, 8);
        bptree.insert(10, 10);
        bptree.insert(14, 14);
        bptree.insert(19, 19);

        bptree.remove(&10329);
        // println!("Nice{:#?}\n", bptree.root);
        bptree.remove(&14);
        assert!(bptree.search(&14).is_none());
        // println!("Nice{:#?}\n", bptree.root);
        bptree.remove(&10);
        assert!(bptree.search(&10).is_none());
        println!("Nice{:#?}\n", bptree.root);

        bptree.search(&8).safe_read(|val| assert_eq!(*val, 8));
        bptree.search(&19).safe_read(|val| assert_eq!(*val, 19));
        bptree.remove(&19);
        assert!(bptree.search(&19).is_none());
        bptree.search(&8).safe_read(|val| assert_eq!(*val, 8));
        bptree.remove(&8);
        assert!(bptree.search(&8).is_none());
    }

    #[test]
    fn test_remove_2() {
        let values = [6, 7, 4, 9, 8, 1];
        let mut bptree = BPTree::<3, i32, i32>::new();

        for value in values {
            bptree.insert(value, value);
        }

        let removal_order = [1, 4, 7, 6, 8, 9];
        for i in 0..removal_order.len() {
            let removal = removal_order[i];
            bptree.remove(&removal);
            assert!(bptree.search(&removal).is_none());

            for j in i + 1..removal_order.len() {
                assert_eq!(
                    bptree
                        .search(&removal_order[j])
                        .safe_read(|val| val.clone()),
                    removal_order[j]
                )
            }
        }
    }

    #[test]
    fn test_remove_3() {
        let values: Vec<usize> = vec![
            59, 88, 83, 41, 76, 62, 72, 29, 74, 70, 23, 84, 51, 98, 73, 93, 66, 17, 16, 9, 35, 27,
            13, 40, 56, 77, 60, 90, 53, 42, 50, 92, 64, 4, 52, 39, 61, 21, 32, 45, 68, 20, 18, 6,
            15, 34, 31, 69, 82, 14, 3, 48, 71, 28, 54, 12, 46, 33, 19, 79, 7, 11, 80, 47, 25, 86,
            43, 1, 78, 36, 91, 26, 58, 8, 57, 87, 24, 67, 30, 65, 38, 99, 10, 75, 55, 22, 63, 95,
            96, 97, 0, 37, 89, 85, 5, 94, 44, 81, 2, 49,
        ];
        let mut bptree: BPTree<3, usize, usize> = BPTree::new();
        for value in &values {
            bptree.insert(*value, *value)
        }

        let removal_order = [
            52, 62, 40, 93, 89, 29, 74, 49, 79, 54, 11, 82, 84, 76, 87, 69, 48, 5, 66, 28, 31, 44,
            73, 22, 59, 12, 0, 24, 21, 7, 61, 2, 71, 6, 19, 17, 85, 33, 8, 42, 96, 88, 38, 67, 60,
            9, 45, 95, 94, 51, 4, 99, 37, 83, 15, 81, 50, 23, 57, 68, 53, 92, 26, 39, 34, 86, 10,
            1, 90, 80, 46, 27, 91, 97, 77, 75, 18, 30, 63, 78, 14, 43, 16, 32, 35, 72, 20, 64, 41,
            47, 55, 58, 13, 98, 70, 25, 56, 65, 36, 3,
        ];

        for i in 0..removal_order.len() {
            let removal = removal_order[i];
            bptree.remove(&removal);
            assert!(bptree.search(&removal).is_none());

            for j in i + 1..removal_order.len() {
                assert_eq!(
                    bptree
                        .search(&removal_order[j])
                        .safe_read(|val| val.clone()),
                    removal_order[j]
                )
            }
        }

        sizes_remove_helper(&values, true);
    }

    #[cfg(feature = "stress")]
    mod stress_tests {
        use super::*;
        use std::fs::File;
        use std::io::BufRead;
        use std::io::BufReader;
        #[test]
        fn test_insert_stress_1() {
            let (keys, values, expected) =
                read_from_insert_file(String::from("src/btree/golden/stress_test_insert_1.golden"));
            sizes_insert_helper(&keys, &values, &expected, false);
        }
        #[test]
        fn test_insert_stress_2() {
            let (keys, values, expected) =
                read_from_insert_file(String::from("src/btree/golden/stress_test_insert_2.golden"));
            sizes_insert_helper(&keys, &values, &expected, false);
        }
        #[test]
        fn test_insert_stress_3() {
            let (keys, values, expected) =
                read_from_insert_file(String::from("src/btree/golden/stress_test_insert_3.golden"));
            sizes_insert_helper(&keys, &values, &expected, false);
        }

        #[test]
        fn test_remove_stress_1() {
            let values =
                read_from_remove_file(String::from("src/btree/golden/stress_test_remove_1.golden"));

            sizes_remove_helper(&values, false);
            let a = &values[0..values.len() / 200];
            sizes_remove_helper(a, true);
        }

        #[test]
        fn test_remove_stress_2() {
            let values =
                read_from_remove_file(String::from("src/btree/golden/stress_test_remove_2.golden"));

            sizes_remove_helper(&values, false);
            let a = &values[0..values.len() / 200];
            sizes_remove_helper(a, true);
        }

        #[test]
        fn test_remove_stress_3() {
            let values =
                read_from_remove_file(String::from("src/btree/golden/stress_test_remove_3.golden"));

            sizes_remove_helper(&values, false);
            let a = &values[0..values.len() / 200];
            sizes_remove_helper(a, true);
        }

        fn read_from_insert_file(file_name: String) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
            let file = File::open(file_name).expect("file wasn't found.");
            let reader = BufReader::new(file);
            let numbers: Vec<usize> = reader
                .lines()
                .map(|line| line.unwrap().parse::<usize>().unwrap())
                .collect();

            let n = numbers[0];

            (
                numbers[1..n + 1].to_vec(),
                numbers[n + 1..2 * n + 1].to_vec(),
                numbers[2 * n + 1..numbers.len()].to_vec(),
            )
        }

        fn read_from_remove_file(file_name: String) -> Vec<usize> {
            let file = File::open(file_name).expect("file wasn't found.");
            let reader = BufReader::new(file);
            reader
                .lines()
                .map(|line| line.unwrap().parse::<usize>().unwrap())
                .collect()
        }
    }

    fn sizes_insert_helper(keys: &[usize], values: &[usize], expected: &[usize], verify: bool) {
        macro_rules! SIZES_TEST {
            ($size: expr) => {
                let mut bptree: BPTree<$size, usize, usize> = BPTree::new();

                for i in 0..keys.len() {
                    bptree.insert(keys[i], values[i]);
                    let start = if verify { 0 } else { i };

                    for j in start..=i {
                        let res = bptree.search(&keys[j]).unwrap();
                        let lock = res.read().unwrap();
                        assert_eq!(*lock, values[j]);
                        drop(lock);
                    }
                }

                let res = bptree.search_range((&0, &(std::usize::MAX - 1)));
                assert_eq!(res.len(), expected.len());

                for i in 0..res.len() {
                    let lock = res[i].read().unwrap();
                    assert_eq!(*lock, expected[i]);
                    drop(lock);
                }
            };
        }
        SIZES_TEST!(5);
        SIZES_TEST!(6);
        SIZES_TEST!(7);
        SIZES_TEST!(22);
        SIZES_TEST!(255);
        SIZES_TEST!(2);
    }

    fn sizes_remove_helper(values: &[usize], verify: bool) {
        macro_rules! SIZES_TEST {
            ($size: expr) => {
                let mut bptree: BPTree<$size, usize, usize> = BPTree::new();
                for value in values {
                    bptree.insert(*value, *value);
                    bptree.search(value).safe_read(|val| assert_eq!(val, value));
                }
                for i in 0..values.len() {
                    let value = &values[i];
                    bptree.remove(value);
                    assert!(bptree.search(value).is_none());

                    if verify {
                        for j in i + 1..values.len() {
                            assert_eq!(
                                bptree.search(&values[j]).safe_read(|val| val.clone()),
                                values[j]
                            )
                        }
                    }
                }
            };
        }

        SIZES_TEST!(5);
        SIZES_TEST!(6);
        SIZES_TEST!(7);
        SIZES_TEST!(22);
        SIZES_TEST!(255);
        SIZES_TEST!(2);
    }
}
