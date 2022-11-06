use std::sync::{Arc, RwLock};

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
        {
            let leaf_node = leaf_lock.unwrap_leaf();

            while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() < start {
                i += 1;
            }
            if i >= leaf_node.num_keys {
                return res;
            }
        }

        drop(leaf_lock);

        while !leaf.is_none() {
            let next;
            let leaf_lock = leaf.as_ref().unwrap().read().unwrap();
            {
                let leaf_node = leaf_lock.unwrap_leaf();

                while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() <= end {
                    res.push(leaf_node.records[i].as_ref().unwrap().clone());
                    i += 1;
                }
                next = leaf_node.next.clone();

                if i != leaf_node.num_keys {
                    break;
                }
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
        // There are 4 cases for insert

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

        // 3 - Desired leaf needs to be split since it has no space
        let leaf = leaf_lock.unwrap_leaf_mut();
        if leaf.num_keys == FANOUT - 1 {
            let mut new_leaf: Leaf<K, V, FANOUT> = Node::new_leaf();
            let split = FANOUT / 2;
            let mut insertion_idx = 0;
            while insertion_idx < leaf.num_keys && leaf.keys[insertion_idx].as_ref().unwrap() < key
            {
                insertion_idx += 1;
            }

            // The node has FANOUT - 1 keys, so we split at (FANOUT - 1) / 2
            // Example, if FANOUT is 3, there are 2 keys (and 2 records since it's a leaf node)
            // Thus, split is at (3 / 2 = 1), and so we keep 1 key in this node, and the others in another node
            // if FANOUT is 4, there are 3 keys. Split is at (4 / 2 = 2). So we keep 2 keys in this node, and put
            // 1 keys in the new node. So there is split keys in the left half and n - split keys in the right half
            // we want the first 0

            let num_total_keys = FANOUT;
            let mut cur = 0;
            let mut old_read_idx = leaf.num_keys - 1;
            while cur < num_total_keys {
                let write_idx = num_total_keys - cur - 1;
                // insert in new leaf
                if write_idx >= split {
                    let new_write_idx = write_idx - split;
                    if write_idx == insertion_idx {
                        new_leaf.keys[new_write_idx] = Some(key.clone());
                        new_leaf.records[new_write_idx] =
                            Some(Arc::new(RwLock::new(record.clone())));
                    } else {
                        new_leaf.keys[new_write_idx] = leaf.keys[old_read_idx].clone();
                        new_leaf.records[new_write_idx] = leaf.records[old_read_idx].clone();
                        leaf.keys[old_read_idx] = None;
                        leaf.records[old_read_idx] = None;

                        // to prevent overflow
                        if old_read_idx > 0 {
                            old_read_idx -= 1;
                        }
                    }
                }
                // insert in old leaf
                else {
                    if write_idx == insertion_idx {
                        leaf.keys[write_idx] = Some(key.clone());
                        leaf.records[write_idx] = Some(Arc::new(RwLock::new(record.clone())));
                    } else {
                        leaf.keys.swap(write_idx, old_read_idx);

                        // to prevent overflow
                        if old_read_idx > 0 {
                            old_read_idx -= 1;
                        }
                    }
                }
                cur += 1
            }

            leaf.num_keys = split;
            new_leaf.num_keys = num_total_keys - split;
            new_leaf.parent = leaf.parent.clone();
            drop(leaf_lock);
            self.insert_into_parent(
                leaf_node,
                &new_leaf.keys[0].clone().unwrap(),
                Arc::new(RwLock::new(Node::Leaf(new_leaf))),
            );
            return;
        }

        // 4 - Desired leaf has space, let's insert it here
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
    }

    fn insert_into_parent(
        &mut self,
        left: NodePtr<K, V, FANOUT>,
        key: &K,
        right: NodePtr<K, V, FANOUT>,
    ) {
        let mut left_lock = left.write().unwrap();
        let parent = match &*left_lock {
            Node::Leaf(leaf) => leaf.parent.as_ref(),
            Node::Invalid => panic!("Invalid node"),
            Node::Interior(node) => node.parent.as_ref(),
        };

        // 3 cases for insert into parent
        // 1 - No parent for left/right. We need to make a new root node if there is no parent
        if parent.is_none() {
            let mut new_node: Interior<K, V, FANOUT> = Node::new_interior();
            new_node.keys[0] = Some(key.clone());
            new_node.children[0] = Some(left.clone());
            new_node.children[1] = Some(right.clone());
            new_node.num_keys = 1;
            self.root = Some(Arc::new(RwLock::new(Node::Interior(new_node))));

            match &mut *left_lock {
                Node::Invalid => panic!("Invalid Node"),
                Node::Leaf(leaf) => {
                    leaf.parent = Some(Arc::downgrade(&self.root.as_ref().unwrap()));
                    leaf.next = Some(Arc::downgrade(&right));
                }
                Node::Interior(node) => {
                    node.parent = Some(Arc::downgrade(&self.root.as_ref().unwrap()));
                }
            }
            drop(left_lock);

            let mut right_lock = right.write().unwrap();
            match &mut *right_lock {
                Node::Invalid => panic!("Invalid Node"),
                Node::Leaf(leaf) => {
                    leaf.parent = Some(Arc::downgrade(&self.root.as_ref().unwrap()));
                    leaf.prev = Some(Arc::downgrade(&left));
                }
                Node::Interior(node) => {
                    node.parent = Some(Arc::downgrade(&self.root.as_ref().unwrap()));
                }
            }
            drop(right_lock);
            return;
        }
        let parent = parent.unwrap().upgrade().unwrap();
        // TODO: 2 - interior node has no space so we have to split it
        // TODO: 3 - interior node has space so we just have to insert key / record
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

                while i < node.num_keys && *key >= *node.keys[i].as_ref()? {
                    i += 1
                }
                node.children[i].as_ref()?.clone()
            };

            drop(lock);
            cur = next;
        }
        Some(cur)
    }
}

impl Key for i32 {}

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
    }
}
