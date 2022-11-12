use super::{node::*, typedefs::*};
use std::mem;
use std::sync::{Arc, RwLock};

#[derive(Debug)]
pub struct BPTree<const FANOUT: usize, K: Key, T: Record> {
    root: Option<NodePtr<FANOUT, K, T>>,
}

impl<const FANOUT: usize, K: Key, T: Record> BPTree<FANOUT, K, T> {
    pub fn new() -> Self {
        assert!(FANOUT > 1);
        Self { root: None }
    }

    pub fn search(&self, key: &K) -> Option<RecordPtr<T>> {
        let leaf = self.get_leaf_node(key)?;
        let lock = leaf.read().ok()?;
        let leaf = lock.get_leaf()?;
        for i in 0..leaf.num_keys {
            if *key == *leaf.keys[i].as_ref()? {
                return Some(leaf.records[i].as_ref()?.clone());
            }
        }
        None
    }

    pub fn search_range(&self, (start, end): (&K, &K)) -> Vec<RecordPtr<T>> {
        assert!(end >= start);

        let mut result: Vec<RecordPtr<T>> = Vec::new();

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

    pub fn insert(&mut self, key: K, record: T) {
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
            let mut new_leaf: Leaf<FANOUT, K, T> = Node::new_leaf();
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

    pub fn remove(&mut self, key: &K) {}

    /* private */
    fn insert_into_parent(
        &mut self,
        left: NodePtr<FANOUT, K, T>,
        key: K,
        right: NodePtr<FANOUT, K, T>,
    ) {
        let left_lock = left.read().unwrap();
        let parent = left_lock.get_parent();
        drop(left_lock);

        // 2 cases for insert into parent
        // 1 - No parent for left/right. We need to make a new root node if there is no parent
        if parent.is_none() {
            let mut new_node: Interior<FANOUT, K, T> = Node::new_interior();
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
            let mut new_interior: Interior<FANOUT, K, T> = Node::new_interior();
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

    /* private */
    fn get_leaf_node(&self, key: &K) -> Option<NodePtr<FANOUT, K, T>> {
        let mut current = self.root.clone()?;
        loop {
            let lock = current.read().unwrap();
            if lock.get_interior().is_none() {
                break;
            }

            let next = {
                let mut i = 0;
                let node = lock.get_interior()?;
                while i < node.num_keys && *key >= *node.keys[i].as_ref()? {
                    i += 1;
                }
                node.children[i].as_ref()?.clone()
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
    use std::fs::File;
    use std::io::BufRead;
    use std::io::BufReader;
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
                .search_range((&0, &9))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![1, 2, 4, 9],
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
                .search_range((&16, &21))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18, 19, 21],
        );

        assert_eq!(
            bptree
                .search_range((&16, &21))
                .iter()
                .map(|item| item.try_read().unwrap().clone())
                .collect::<Vec<i32>>(),
            vec![18, 19, 21],
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

        sizes_helper(&keys, &values, &expected, true);
    }

    #[test]
    fn test_insert_small() {
        let keys: Vec<usize> = vec![9, 7, 1, 7, 4, 5, 5, 2, 1, 9];
        let values: Vec<usize> = vec![89, 3, 54, 90, 19, 2, 44, 85, 94, 10];
        let expected: Vec<usize> = vec![94, 85, 19, 44, 90, 10];
        sizes_helper(&keys, &values, &expected, false);
    }

    #[cfg(feature = "stress")]
    mod stress_tests {
        use super::*;
        #[test]
        fn test_insert_stress() {
            let (keys, values, expected) =
                read_from_file(String::from("src/btree/golden/stress_test_2.golden"));
            sizes_helper(&keys, &values, &expected, false);
        }

        fn read_from_file(file_name: String) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
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
    }

    fn sizes_helper(keys: &[usize], values: &[usize], expected: &[usize], verify: bool) {
        macro_rules! SIZES_TEST {
            ($size: expr, $optimize: expr) => {
                let mut bptree: BPTree<$size, usize, usize> = BPTree::new();

                for i in 0..keys.len() {
                    bptree.insert(keys[i], values[i]);
                    let start = if verify { 0 } else { i };

                    if (!$optimize) {
                        for j in start..=i {
                            let res = bptree.search(&keys[j]).unwrap();
                            let lock = res.read().unwrap();
                            assert_eq!(*lock, values[j]);
                            drop(lock);
                        }
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
        SIZES_TEST!(5, false);
        SIZES_TEST!(6, false);
        SIZES_TEST!(7, false);
        SIZES_TEST!(22, false);
        SIZES_TEST!(255, false);
        SIZES_TEST!(2, false);
    }
}
