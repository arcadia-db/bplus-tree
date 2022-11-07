use std::{
    mem::swap,
    sync::{Arc, RwLock},
};

use crate::btree::node::*;
#[derive(Debug)]
pub struct BPTree<K: Key, V: Record, const FANOUT: usize> {
    root: Option<NodePtr<K, V, FANOUT>>,
}

impl<K: Key, V: Record, const FANOUT: usize> BPTree<K, V, FANOUT> {
    pub fn new() -> Self {
        assert!(FANOUT >= 2);
        Self { root: None }
    }

    pub fn search(&self, key: &K) -> Option<RecordPtr<V>> {
        let leaf = self.get_leaf_node(key)?;
        let leaf_lock = leaf.read().unwrap();
        let leaf = leaf_lock.unwrap_leaf();
        for i in 0..leaf.num_keys {
            if *key == *leaf.keys[i].as_ref()? {
                return Some(leaf.records[i].as_ref()?.clone());
            }
        }
        None
    }

    pub fn search_range(&self, start: &K, end: &K) -> Vec<RecordPtr<V>> {
        let mut res = vec![];
        let mut leaf = self.get_leaf_node(start);
        if leaf.is_none() {
            return res;
        }
        // find the position within the leaf
        let mut i = 0;

        let leaf_lock = leaf.as_ref().unwrap().read().unwrap();
        let leaf_node = leaf_lock.unwrap_leaf();

        while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() < start {
            i += 1;
        }
        if i >= leaf_node.num_keys {
            return res;
        }

        drop(leaf_lock);

        while !leaf.is_none() {
            let next;
            let leaf_lock = leaf.as_ref().unwrap().read().unwrap();

            let leaf_node = leaf_lock.unwrap_leaf();

            while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() <= end {
                res.push(leaf_node.records[i].as_ref().unwrap().clone());
                i += 1;
            }
            next = leaf_node.next.clone();

            if i != leaf_node.num_keys {
                break;
            }

            drop(leaf_lock);
            if next.is_none() {
                break;
            }
            leaf = next.unwrap().upgrade();
            i = 0;
        }

        return res;
    }

    pub fn insert(&mut self, key: &K, record: &V) {
        // There are 3 cases for insert

        // 1 - key exists so just update the record
        let searched_record = self.search(key);
        if let Some(value) = searched_record {
            let mut lock = value.write().unwrap();
            *lock = record.clone();
            return;
        }

        // 2 - Empty tree so start a new tree
        if self.root.is_none() {
            let mut new_node = Node::new_leaf();
            new_node.keys[0] = Some(key.clone());
            new_node.records[0] = Some(Arc::new(RwLock::new(record.clone())));
            new_node.num_keys += 1;
            self.root = Some(Arc::new(RwLock::new(Node::Leaf(new_node))));
            return;
        }

        let leaf_node = self.get_leaf_node(key).unwrap();
        let mut leaf_lock = leaf_node.write().unwrap();

        // 3 - Insert into leaf, splitting if needed
        let leaf = leaf_lock.unwrap_leaf_mut();

        let mut insertion_idx = 0;
        while insertion_idx < leaf.num_keys && leaf.keys[insertion_idx].as_ref().unwrap() < key {
            insertion_idx += 1
        }

        let mut i = leaf.num_keys;
        while i > insertion_idx {
            leaf.keys.swap(i, i - 1);
            leaf.records.swap(i, i - 1);
            i -= 1
        }
        leaf.keys[insertion_idx] = Some(key.clone());
        leaf.records[insertion_idx] = Some(Arc::new(RwLock::new(record.clone())));
        leaf.num_keys += 1;

        // split if overflow (this is why we added 1 extra spot in the array)
        if leaf.num_keys == FANOUT {
            let mut new_leaf: Leaf<K, V, FANOUT> = Node::new_leaf();
            let split = FANOUT / 2;

            for i in split..leaf.num_keys {
                swap(&mut new_leaf.keys[i - split], &mut leaf.keys[i]);
                swap(&mut new_leaf.records[i - split], &mut leaf.records[i]);
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

            self.insert_into_parent(leaf_node, &new_key, new_leaf_node);
        }
    }

    fn insert_into_parent(
        &mut self,
        left: NodePtr<K, V, FANOUT>,
        key: &K,
        right: NodePtr<K, V, FANOUT>,
    ) {
        let left_lock = left.read().unwrap();
        let parent = left_lock.get_parent();
        drop(left_lock);

        // 3 cases for insert into parent
        // 1 - No parent for left/right. We need to make a new root node if there is no parent
        if parent.is_none() {
            let mut new_node: Interior<K, V, FANOUT> = Node::new_interior();
            new_node.keys[0] = Some(key.clone());
            new_node.children[0] = Some(left.clone());
            new_node.children[1] = Some(right.clone());
            new_node.num_keys = 1;
            self.root = Some(Arc::new(RwLock::new(Node::Interior(new_node))));

            let mut left_lock = left.write().unwrap();
            left_lock.set_parent(Some(Arc::downgrade(&self.root.as_ref().unwrap())));
            drop(left_lock);

            let mut right_lock = right.write().unwrap();
            right_lock.set_parent(Some(Arc::downgrade(&self.root.as_ref().unwrap())));
            drop(right_lock);
            return;
        }
        let parent_node = parent.unwrap().upgrade().unwrap();
        let mut parent_lock = parent_node.write().unwrap();
        let parent = parent_lock.unwrap_interior_mut();

        // assign right's parent pointer
        let mut right_lock = right.write().unwrap();
        right_lock.set_parent(Some(Arc::downgrade(&parent_node)));
        drop(right_lock);

        let mut left_idx_in_parent = 0;
        while left_idx_in_parent < parent.num_keys
            && !Arc::ptr_eq(
                &parent.children[left_idx_in_parent].as_ref().unwrap(),
                &left,
            )
        {
            left_idx_in_parent += 1
        }

        let mut i = parent.num_keys + 1;
        while i > left_idx_in_parent + 1 {
            parent.keys.swap(i - 1, i - 2);
            parent.children.swap(i, i - 1);
            i -= 1
        }
        parent.keys[left_idx_in_parent] = Some(key.clone());
        parent.children[left_idx_in_parent + 1] = Some(right.clone());
        parent.num_keys += 1;

        // 2 - interior node has no space so we have to split it
        if parent.num_keys == FANOUT {
            let mut new_interior: Interior<K, V, FANOUT> = Node::new_interior();
            let split = (FANOUT + 1) / 2 - 1;

            for i in split + 1..parent.num_keys {
                swap(&mut parent.keys[i], &mut new_interior.keys[i - split - 1]);
                swap(
                    &mut parent.children[i],
                    &mut new_interior.children[i - split - 1],
                );
            }
            let pushed_key = parent.keys[split].as_ref().unwrap().clone();
            swap(
                &mut parent.children[FANOUT],
                &mut new_interior.children[parent.num_keys - split - 1],
            );
            parent.keys[split] = None;

            new_interior.num_keys = parent.num_keys - split - 1;
            parent.num_keys = split;
            new_interior.parent = parent.parent.clone();
            let new_interior_node = Arc::new(RwLock::new(Node::Interior(new_interior)));
            let new_interior_lock = new_interior_node.read().unwrap();
            let new_interior = new_interior_lock.unwrap_interior();

            for i in 0..new_interior.num_keys + 1 {
                let child = new_interior.children[i].as_ref().unwrap();
                let mut child_lock = child.write().unwrap();
                child_lock.set_parent(Some(Arc::downgrade(&new_interior_node)));
                drop(child_lock);
            }
            drop(new_interior_lock);
            drop(parent_lock);
            self.insert_into_parent(parent_node, &pushed_key, new_interior_node);
        }
    }

    /* private */
    fn get_leaf_node(&self, key: &K) -> Option<NodePtr<K, V, FANOUT>> {
        let mut cur = self.root.clone()?;
        loop {
            let lock = cur.read().unwrap();
            if lock.interior().is_none() {
                break;
            }

            let mut i = 0;
            let next = {
                let node = lock.unwrap_interior();

                while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
                    i += 1
                }
                node.children[i].as_ref().unwrap().clone()
            };

            drop(lock);
            cur = next;
        }
        Some(cur)
    }
}

impl Key for i32 {}

impl Record for i32 {}

impl Record for String {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, RwLock};

    #[test]
    fn test_search() {
        const TEST_FANOUT: usize = 2;
        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<i32, String, TEST_FANOUT> = Node::Leaf(Leaf {
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
        let node_leaf2: Node<i32, String, TEST_FANOUT> = Node::Leaf(Leaf {
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
        let node_leaf3: Node<i32, String, TEST_FANOUT> = Node::Leaf(Leaf {
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
        lock.unwrap_leaf_mut().next = Some(Arc::downgrade(&node_leaf2_ptr));
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write().unwrap();
        lock.unwrap_leaf_mut().next = Some(Arc::downgrade(&node_leaf3_ptr));
        drop(lock);

        // Create interior (node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr)
        let node_interior1: Node<i32, String, TEST_FANOUT> = Node::Interior(Interior {
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
        let lock = node_interior1_ptr.write().unwrap();
        for child in &lock.unwrap_interior().children {
            if let Some(ptr) = child.as_ref() {
                let mut ptr_lock = ptr.write().unwrap();
                ptr_lock.unwrap_leaf_mut().parent = Some(Arc::downgrade(&node_interior1_ptr));
                drop(ptr_lock);
            }
        }
        drop(lock);

        // Create B+Tree
        let bptree1: BPTree<i32, String, TEST_FANOUT> = BPTree {
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
        assert_eq!(res.is_none(), true);

        let res = bptree1.search(&3);
        assert_eq!(res.is_none(), true);

        let res = bptree1.search(&14);
        assert_eq!(res.is_none(), true);

        let res = bptree1.search(&21);
        assert_eq!(res.is_none(), true);
    }

    #[test]
    fn test_range_search() {
        const TEST_FANOUT: usize = 2;

        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<i32, String, TEST_FANOUT> = Node::Leaf(Leaf {
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
        let node_leaf2: Node<i32, String, TEST_FANOUT> = Node::Leaf(Leaf {
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
        let node_leaf3: Node<i32, String, TEST_FANOUT> = Node::Leaf(Leaf {
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
        lock.unwrap_leaf_mut().next = Some(Arc::downgrade(&node_leaf2_ptr));
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write().unwrap();
        lock.unwrap_leaf_mut().next = Some(Arc::downgrade(&node_leaf3_ptr));
        drop(lock);

        // Create interior (node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr)
        let node_interior1: Node<i32, String, TEST_FANOUT> = Node::Interior(Interior {
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
        let lock = node_interior1_ptr.write().unwrap();
        for child in &lock.unwrap_interior().children {
            if let Some(ptr) = child.as_ref() {
                let mut ptr_lock = ptr.write().unwrap();
                ptr_lock.unwrap_leaf_mut().parent = Some(Arc::downgrade(&node_interior1_ptr));
                drop(ptr_lock);
            }
        }
        drop(lock);

        // Create B+Tree
        let bptree1: BPTree<i32, String, TEST_FANOUT> = BPTree {
            root: Some(node_interior1_ptr),
        };

        let res = bptree1.search_range(&1, &2);
        let lock = res[0].read().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range(&0, &2);
        let lock = res[0].read().unwrap();
        assert_eq!(*lock, "John");
        drop(lock);
        let lock = res[1].read().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range(&2, &12);
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
    fn test_insert() {
        let mut bptree: BPTree<i32, String, 3> = BPTree::new();
        bptree.insert(&3, &String::from("Emily"));
        bptree.insert(&5, &String::from("Srihari"));

        let res = bptree.search(&3).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Emily");
        drop(lock);

        let res = bptree.search(&5).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Srihari");
        drop(lock);

        // update value of 5
        bptree.insert(&5, &String::from("Cool"));
        let res = bptree.search(&5).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Cool");
        drop(lock);

        // this should trigger a leaf split, and create a new root node
        bptree.insert(&7, &String::from("Rajat"));
        let res = bptree.search(&7).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Rajat");
        drop(lock);

        bptree.insert(&4, &String::from("Erik"));
        let res = bptree.search(&4).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Erik");
        drop(lock);

        // This causes a new leaf node and adding a key to the root internal node
        // println!("{:#?}", bptree);
        bptree.insert(&14, &String::from("Golden"));
        let res = bptree.search(&14).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Golden");
        drop(lock);

        bptree.insert(&16, &String::from("Backpack"));
        println!("{:#?}", bptree);
        let res = bptree.search(&16).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Backpack");
        drop(lock);
    }

    #[test]
    fn test_insert_sequential() {
        let mut bptree: BPTree<i32, String, 3> = BPTree::new();
        bptree.insert(&0, &String::from("Srihari"));
        bptree.insert(&1, &String::from("Vishnu"));
        bptree.insert(&2, &String::from("Rajat"));
        bptree.insert(&3, &String::from("Patwari"));
        bptree.insert(&4, &String::from("Golden"));

        let res = bptree.search(&4).unwrap();
        let lock = res.read().unwrap();
        assert_eq!(*lock, "Golden");
        drop(lock);

        let res = bptree.search_range(&1, &4);

        let expected = ["Vishnu", "Rajat", "Patwari", "Golden"];

        for i in 0..res.len() {
            let lock = res[i].read().unwrap();
            assert_eq!(expected[i], *lock);
            drop(lock);
        }
        // println!("{:#?}", bptree);
    }

    #[test]
    fn test_insert_stress() {
        let keys = [
            4, 56, 81, 71, 57, 62, 12, 91, 31, 58, 92, 37, 61, 11, 98, 75, 17, 35, 36, 23, 39, 95,
            42, 78, 38, 13, 30, 34, 84, 69, 54, 50, 99, 43, 2, 83, 28, 27, 19, 45, 32, 80, 3, 47,
            90, 14, 49, 67, 72, 25, 24, 52, 93, 51, 0, 44, 18, 86, 66, 10, 88, 6, 79, 48, 68, 26,
            33, 21, 60, 73, 41, 29, 87, 89, 97, 40, 94, 8, 20, 15, 1, 74, 59, 70, 96, 16, 22, 77,
            53, 82, 85, 7, 5, 55, 63, 46, 76, 64, 65, 9,
        ];

        let values = [
            99, 27, 34, 37, 23, 38, 47, 67, 45, 17, 3, 50, 5, 70, 3, 53, 26, 36, 69, 68, 56, 77,
            49, 37, 11, 16, 6, 16, 86, 30, 77, 3, 12, 31, 35, 76, 79, 9, 91, 47, 79, 91, 62, 91,
            61, 80, 29, 89, 89, 46, 18, 86, 26, 14, 98, 87, 92, 74, 4, 26, 29, 17, 76, 70, 10, 1,
            75, 50, 20, 50, 47, 15, 44, 30, 78, 3, 69, 22, 60, 88, 48, 32, 32, 73, 73, 16, 85, 50,
            8, 24, 41, 87, 78, 75, 60, 66, 5, 70, 94, 97,
        ];

        let mut bptree: BPTree<i32, i32, 5> = BPTree::new();

        for i in 0..keys.len() {
            bptree.insert(&keys[i], &values[i]);

            for j in 0..=i {
                let res = bptree.search(&keys[j]).unwrap();
                let lock = res.read().unwrap();
                assert_eq!(*lock, values[j]);
                drop(lock);
            }
        }

        let expected = [
            98, 48, 35, 62, 99, 78, 17, 87, 22, 97, 26, 70, 47, 16, 80, 88, 16, 26, 92, 91, 60, 50,
            85, 68, 18, 46, 1, 9, 79, 15, 6, 45, 79, 75, 16, 36, 69, 50, 11, 56, 3, 47, 49, 31, 87,
            47, 66, 91, 70, 29, 3, 14, 86, 8, 77, 75, 27, 23, 17, 32, 20, 5, 38, 60, 70, 94, 4, 89,
            10, 30, 73, 37, 89, 50, 32, 53, 5, 50, 37, 76, 91, 34, 24, 76, 86, 41, 74, 44, 29, 30,
            61, 67, 3, 26, 69, 77, 73, 78, 3, 12,
        ];
        let res = bptree.search_range(&0, &101);
        println!("{:#?}", res);
        assert_eq!(res.len(), keys.len());

        for i in 0..res.len() {
            let lock = res[i].read().unwrap();
            assert_eq!(*lock, expected[i]);
            drop(lock);
        }
    }
}
