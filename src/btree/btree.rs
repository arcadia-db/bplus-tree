use crate::btree::node::*;
#[derive(Debug)]
pub struct BPTree<K: Key, V: Record> {
    root: Option<NodePtr<K, V>>,
}

impl<K: Key, V: Record> BPTree<K, V> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn search(&self, key: &K) -> Option<RecordPtr<V>> {
        let leaf = self.get_leaf_node(key)?;
        let leaf_lock = leaf.read().unwrap();

        let leaf = leaf_lock.unwrap_leaf();
        for i in 0..leaf.size {
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

            while i < leaf_node.size && leaf_node.keys[i].as_ref().unwrap() < start {
                i += 1;
            }
            if i >= leaf_node.size {
                return res;
            }
        }

        drop(leaf_lock);

        while !leaf.is_none() {
            let next;
            let leaf_lock = leaf.as_ref().unwrap().read().unwrap();
            {
                let leaf_node = leaf_lock.unwrap_leaf();

                while i < leaf_node.size && leaf_node.keys[i].as_ref().unwrap() <= end {
                    res.push(leaf_node.records[i].as_ref().unwrap().clone());
                    i += 1;
                }
                next = leaf_node.next.clone();

                if i != leaf_node.size {
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

    pub fn insert(&self, key: &K, record: &V) {}

    /* private */
    fn get_leaf_node(&self, key: &K) -> Option<NodePtr<K, V>> {
        let mut cur = self.root.clone()?;

        loop {
            let lock = cur.read().ok()?;
            if lock.interior().is_none() {
                break;
            }

            let mut i = 0;
            let next = {
                let node = lock.unwrap_interior();

                while i < node.size && *key >= *node.keys[i].as_ref()? {
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
    use std::sync::{Arc, RwLock, Weak};

    #[test]
    fn test_search() {
        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<i32, String> = Node::Leaf(Leaf {
            size: 2,
            keys: [Some(0), Some(2)],
            records: [
                Some(Arc::new(RwLock::new(String::from("John")))),
                Some(Arc::new(RwLock::new(String::from("Adam")))),
            ],
            parent: None,
            prev: None,
            next: None,
        });
        let node_leaf1_ptr = Arc::new(RwLock::new(node_leaf1));

        // Create node (10 = "Emily"), (12 = "Jessica")
        let node_leaf2: Node<i32, String> = Node::Leaf(Leaf {
            size: 2,
            keys: [Some(10), Some(12)],
            records: [
                Some(Arc::new(RwLock::new(String::from("Emily")))),
                Some(Arc::new(RwLock::new(String::from("Jessica")))),
            ],
            parent: None,
            prev: Some(Arc::downgrade(&node_leaf1_ptr)),
            next: None,
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(node_leaf2));

        // Create node (20 = "Sam")
        let node_leaf3: Node<i32, String> = Node::Leaf(Leaf {
            size: 1,
            keys: [Some(20), None],
            records: [Some(Arc::new(RwLock::new(String::from("Sam")))), None],
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
        let node_interior1: Node<i32, String> = Node::Interior(Interior {
            size: 2,
            keys: [Some(10), Some(20)],
            children: [
                Some(node_leaf1_ptr),
                Some(node_leaf2_ptr),
                Some(node_leaf3_ptr),
            ],
        });
        let node_interior1_ptr = Arc::new(RwLock::new(node_interior1));

        // Set all children of node_interior1's ptr_leaf_parent to node_interior1
        let lock = node_interior1_ptr.write().unwrap();
        for child in lock.unwrap_interior().children.as_ref() {
            if let Some(ptr) = child.as_ref() {
                let mut ptr_lock = ptr.write().unwrap();
                ptr_lock.unwrap_leaf_mut().parent = Some(Arc::downgrade(&node_interior1_ptr));
                drop(ptr_lock);
            }
        }
        drop(lock);

        // Create B+Tree
        let bptree1: BPTree<i32, String> = BPTree {
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
        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<i32, String> = Node::Leaf(Leaf {
            size: 2,
            keys: [Some(0), Some(2)],
            records: [
                Some(Arc::new(RwLock::new(String::from("John")))),
                Some(Arc::new(RwLock::new(String::from("Adam")))),
            ],
            parent: None,
            prev: None,
            next: None,
        });
        let node_leaf1_ptr = Arc::new(RwLock::new(node_leaf1));

        // Create node (10 = "Emily"), (12 = "Jessica")
        let node_leaf2: Node<i32, String> = Node::Leaf(Leaf {
            size: 2,
            keys: [Some(10), Some(12)],
            records: [
                Some(Arc::new(RwLock::new(String::from("Emily")))),
                Some(Arc::new(RwLock::new(String::from("Jessica")))),
            ],
            parent: None,
            prev: Some(Arc::downgrade(&node_leaf1_ptr)),
            next: None,
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(node_leaf2));

        // Create node (20 = "Sam")
        let node_leaf3: Node<i32, String> = Node::Leaf(Leaf {
            size: 1,
            keys: [Some(20), None],
            records: [Some(Arc::new(RwLock::new(String::from("Sam")))), None],
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
        let node_interior1: Node<i32, String> = Node::Interior(Interior {
            size: 2,
            keys: [Some(10), Some(20)],
            children: [
                Some(node_leaf1_ptr),
                Some(node_leaf2_ptr),
                Some(node_leaf3_ptr),
            ],
        });
        let node_interior1_ptr = Arc::new(RwLock::new(node_interior1));

        // Set all children of node_interior1's ptr_leaf_parent to node_interior1
        let lock = node_interior1_ptr.write().unwrap();
        for child in lock.unwrap_interior().children.as_ref() {
            if let Some(ptr) = child.as_ref() {
                let mut ptr_lock = ptr.write().unwrap();
                ptr_lock.unwrap_leaf_mut().parent = Some(Arc::downgrade(&node_interior1_ptr));
                drop(ptr_lock);
            }
        }
        drop(lock);

        // Create B+Tree
        let bptree1: BPTree<i32, String> = BPTree {
            root: Some(node_interior1_ptr),
        };

        let res = bptree1.search_range(&1, &2);
        let lock = res[0].read().ok().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range(&0, &2);
        let lock = res[0].read().ok().unwrap();
        assert_eq!(*lock, "John");
        drop(lock);
        let lock = res[1].read().ok().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range(&2, &12);
        let lock = res[0].read().ok().unwrap();
        assert_eq!(*lock, "Adam");
        drop(lock);
        let lock = res[1].read().ok().unwrap();
        assert_eq!(*lock, "Emily");
        drop(lock);
        let lock = res[2].read().ok().unwrap();
        assert_eq!(*lock, "Jessica");
        drop(lock);
    }
}
