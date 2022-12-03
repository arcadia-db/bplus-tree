use crate::node::interior::Interior;
use crate::node::node::Node;

use super::{conc::*, typedefs::*};

use parking_lot::RwLock;
use std::sync::Arc;
use std::time::Duration;
use std::vec;

#[derive(Debug, Clone)]
pub struct BPTree<const FANOUT: usize, K: Key, V: Record> {
    root: NodePtr<FANOUT, K, V>,
}
impl<const FANOUT: usize, K: Key, V: Record> Default for BPTree<FANOUT, K, V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<const FANOUT: usize, K: Key, V: Record> BPTree<FANOUT, K, V> {
    pub fn new() -> Self {
        assert!(FANOUT > 1);
        Self {
            root: Node::new_empty(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.root.read().is_none()
    }

    pub fn search(&self, key: &K) -> Option<RecordPtr<V>> {
        let leaf_traversal = self.get_leaf_shared(key);
        let lock = leaf_traversal.lock;
        if lock.is_none() {
            return None;
        }
        let leaf = lock.as_ref().unwrap().get_leaf().unwrap();
        for i in 0..leaf.num_keys {
            if *key == *leaf.keys[i].as_ref().unwrap() {
                return Some(leaf.records[i].clone());
            }
        }
        None
    }

    pub fn search_range(&self, (start, end): (&K, &K)) -> Vec<RecordPtr<V>> {
        if end < start {
            return vec![];
        }

        // this loop is used to retry the search if
        // we enter a deadlock situation
        loop {
            let mut result: Vec<RecordPtr<V>> = Vec::new();

            let traversal = self.get_leaf_shared(start);
            // the only case the traversal is none is if the root node is None (empty tree)
            if traversal.lock.is_none() {
                return result;
            }

            let mut leaf_lock = traversal.lock;

            // Find position within leaf
            let mut leaf = leaf_lock.as_ref().unwrap().get_leaf().unwrap();

            // this loops through leaf nodes + records that fall in the given range
            loop {
                let mut i = 0;
                while i < leaf.num_keys && leaf.keys[i].as_ref().unwrap() <= end {
                    if leaf.keys[i].as_ref().unwrap() >= start {
                        result.push(leaf.records[i].clone());
                    }
                    i += 1;
                }
                if i != leaf.num_keys {
                    return result;
                }
                let temp = leaf.next.upgrade();
                if temp.is_none() {
                    return result;
                }

                let cur_lock_attempt = temp
                    .as_ref()
                    .unwrap()
                    .try_read_arc_for(Duration::from_micros(10));

                if let Some(guard) = cur_lock_attempt {
                    leaf_lock = guard;
                    leaf = leaf_lock.as_ref().unwrap().get_leaf().unwrap();
                } else {
                    break;
                }
            }
        }
    }

    pub fn insert(&self, key: K, record: V) {
        // optimistic latching
        let mut ancestor_latches =
            self.get_leaf_optimistic(&key, |node| node.has_space_for_insert());

        let ExclusiveLatchInfo {
            lock: mut leaf_lock,
            node: leaf_node,
        } = ancestor_latches.pop().unwrap();

        // 1 - Empty tree so start a new tree
        if leaf_lock.is_none() {
            let mut new_node = Node::new_leaf();
            new_node.keys[0] = Some(key);
            new_node.records[0] = Arc::new(RwLock::new(Some(record)));
            new_node.num_keys += 1;
            *leaf_lock = Some(Node::Leaf(new_node));
            return;
        }

        // 2 - Insert into leaf
        let leaf = leaf_lock.as_mut().unwrap().get_leaf_mut().unwrap();
        leaf.insert(key, record);

        // split if overflow (this is why we added 1 extra spot in the array)
        if leaf.num_keys == FANOUT {
            let (new_key, new_leaf_node) = leaf.split(leaf_node);
            self.insert_into_parent(leaf_lock, new_key, new_leaf_node, ancestor_latches);
        }
    }

    pub fn remove(&self, key: &K) {
        let ancestor_latches = self.get_leaf_optimistic(key, |node| node.has_space_for_removal());

        // tree is empty
        if ancestor_latches.is_empty() || ancestor_latches.last().is_none() {
            return;
        }
        self.remove_helper(Some(key), None, None, ancestor_latches)
    }

    /* private */
    fn insert_into_parent(
        &self,
        mut left_lock: parking_lot::lock_api::ArcRwLockWriteGuard<
            parking_lot::RawRwLock,
            Option<Node<FANOUT, K, V>>,
        >,
        key: K,
        right: NodePtr<FANOUT, K, V>,
        mut ancestor_latches: Vec<ExclusiveLatchInfo<FANOUT, K, V>>,
    ) {
        // No parent for left/right. We need to make a new root node if there is no parent
        if ancestor_latches.is_empty() {
            let mut new_node: Interior<FANOUT, K, V> = Node::new_interior();
            new_node.keys[0] = Some(key);
            new_node.children[0] = Arc::new(RwLock::new(left_lock.clone()));
            new_node.children[1] = right;
            new_node.num_keys = 1;
            *left_lock = Some(Node::Interior(new_node));
            return;
        }
        drop(left_lock);

        let ExclusiveLatchInfo {
            lock: mut parent_lock,
            node: _,
        } = ancestor_latches.pop().unwrap();

        let parent = parent_lock.as_mut().unwrap().get_interior_mut().unwrap();
        parent.insert(key, right);

        // interior node has no space so we have to split it
        if parent.num_keys == FANOUT {
            let (pushed_key, new_interior_node) = parent.split();
            self.insert_into_parent(parent_lock, pushed_key, new_interior_node, ancestor_latches);
        }
    }

    /* private */
    fn remove_helper(
        &self,
        key: Option<&K>,
        left_child_lock: Option<
            parking_lot::lock_api::ArcRwLockWriteGuard<
                parking_lot::RawRwLock,
                Option<Node<FANOUT, K, V>>,
            >,
        >,
        right_child: Option<&NodePtr<FANOUT, K, V>>,
        mut ancestor_latches: Vec<ExclusiveLatchInfo<FANOUT, K, V>>,
    ) {
        let ExclusiveLatchInfo { mut lock, node } = ancestor_latches.pop().unwrap();
        let lock_unwrapped = lock.as_ref().unwrap();

        // check whether this node is the root and will be deleted either way
        if Arc::ptr_eq(&node, &self.root) && lock_unwrapped.get_num_keys() == 1 {
            if let Some(Node::Interior(_)) = &*lock {
                *lock = left_child_lock.unwrap().clone();
            } else {
                *lock = None;
            }
            return;
        }

        // perform the removal
        match lock.as_mut().unwrap() {
            Node::Invalid => panic!("{}", "Invalid Node"),
            Node::Leaf(leaf) => leaf.remove(key.unwrap()),
            Node::Interior(node) => node.remove(right_child.unwrap()),
        }

        // if this is the root, we don't care about underfull conditions
        if Arc::ptr_eq(&node, &self.root) {
            return;
        }

        let lock_unwrapped = lock.as_mut().unwrap();

        // if we have enough keys, we are done
        if !lock_unwrapped.is_underfull() {
            return;
        }

        let ExclusiveLatchInfo {
            lock: mut parent_lock,
            node: parent_node,
        } = ancestor_latches.pop().unwrap();

        let parent = parent_lock.as_mut().unwrap().get_interior_mut().unwrap();
        let mut i = 0;
        while i <= parent.num_keys && !Arc::ptr_eq(&node, &parent.children[i]) {
            i += 1;
        }
        let discriminator;
        let sibling_node;
        let is_sibling_successor;

        if i < parent.num_keys {
            discriminator = parent.keys[i].clone().unwrap();
            sibling_node = parent.children[i + 1].clone();
            is_sibling_successor = true;
        } else {
            discriminator = parent.keys[i - 1].clone().unwrap();
            sibling_node = parent.children[i - 1].clone();
            is_sibling_successor = false;
        }
        let mut sibling_lock = sibling_node.write_arc();

        // we either borrow from sibling if it has enough keys
        if sibling_lock.as_ref().unwrap().get_num_keys() > FANOUT / 2 {
            let to_replace = if is_sibling_successor {
                lock_unwrapped
                    .borrow_from_successor(sibling_lock.as_mut().unwrap(), discriminator.clone())
            } else {
                lock_unwrapped
                    .borrow_from_predecessor(sibling_lock.as_mut().unwrap(), discriminator.clone())
            };
            for parent_key in &mut parent.keys {
                if *parent_key.as_ref().unwrap() == discriminator {
                    *parent_key = to_replace;
                    break;
                }
            }
        }
        // or we merge with the sibling
        else {
            if is_sibling_successor {
                lock_unwrapped.merge(sibling_lock.as_mut().unwrap(), discriminator);
            } else {
                sibling_lock
                    .as_mut()
                    .unwrap()
                    .merge(lock_unwrapped, discriminator);
            }

            let (left_lock, right_child) = if is_sibling_successor {
                drop(sibling_lock);
                (lock, sibling_node)
            } else {
                drop(lock);
                (sibling_lock, node)
            };

            ancestor_latches.push(ExclusiveLatchInfo {
                lock: parent_lock,
                node: parent_node,
            });
            self.remove_helper(None, Some(left_lock), Some(&right_child), ancestor_latches);
        }
    }

    /* private */
    fn get_leaf_shared(&self, key: &K) -> SharedLatchInfo<FANOUT, K, V> {
        let mut current_node = self.root.clone();
        let mut lock = current_node.read_arc();

        while lock.is_some() && lock.as_ref().unwrap().is_interior() {
            current_node = {
                let mut i = 0;
                let node = lock.as_ref().unwrap().get_interior().unwrap();
                while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
                    i += 1;
                }
                node.children[i].clone()
            };

            let _old_lock = lock;
            lock = current_node.read_arc();
        }
        SharedLatchInfo {
            node: current_node,
            lock,
        }
    }

    fn get_leaf_exclusive<F>(
        &self,
        key: &K,
        clear_ancestors_latches: F,
    ) -> Vec<ExclusiveLatchInfo<FANOUT, K, V>>
    where
        F: Fn(&Node<FANOUT, K, V>) -> bool,
    {
        let mut current_node = self.root.clone();
        let mut lock = current_node.write_arc();
        let mut latches: Vec<ExclusiveLatchInfo<FANOUT, K, V>> = Vec::new();

        while lock.is_some() && lock.as_ref().unwrap().is_interior() {
            let old_node = current_node;
            current_node = {
                let mut i = 0;
                let node = lock.as_ref().unwrap().get_interior().unwrap();
                while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
                    i += 1;
                }
                node.children[i].clone()
            };

            latches.push(ExclusiveLatchInfo {
                lock,
                node: old_node,
            });

            lock = current_node.write_arc();

            // if we are sure that this node will not undergo any
            // structural changes, we can release the latches on all ancestors
            if clear_ancestors_latches(lock.as_ref().unwrap()) {
                // TODO: check that locks are dropped in order
                latches.clear();
            }
        }

        latches.push(ExclusiveLatchInfo {
            lock,
            node: current_node,
        });
        latches
    }

    fn get_leaf_optimistic<F>(
        &self,
        key: &K,
        clear_ancestors_latches: F,
    ) -> Vec<ExclusiveLatchInfo<FANOUT, K, V>>
    where
        F: Fn(&Node<FANOUT, K, V>) -> bool,
    {
        // TODO: look into upgradable lock for optimistic latching

        // let leaf_traversal_optimistic = self.get_leaf_shared(key);

        // // we are safe from splitting so optimistic was good, and we upgrade to write latch
        // if leaf_traversal_optimistic.lock.is_none()
        //     || clear_ancestors_latches(leaf_traversal_optimistic.lock.as_ref().unwrap())
        // {
        //     vec![SharedLatchInfo::upgrade(leaf_traversal_optimistic)]
        // }
        // // if the leaf will require a split / merge, so restart with exclusive
        // else {
        //     drop(leaf_traversal_optimistic);

        // let mut current_node = self.root.clone();
        // let mut lock = current_node.read_arc();

        // while lock.is_some() && lock.as_ref().unwrap().is_interior() {
        //     current_node = {
        //         let mut i = 0;
        //         let node = lock.as_ref().unwrap().get_interior().unwrap();
        //         while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
        //             i += 1;
        //         }
        //         node.children[i].clone()
        //     };

        //     let _old_lock = lock;
        //     lock = current_node.read_arc();
        // }

        self.get_leaf_exclusive(key, clear_ancestors_latches)
    }
}

#[cfg(test)]
mod tests {
    use crate::node::{interior::Interior, leaf::Leaf};

    use super::*;
    use std::sync::{Arc, Weak};

    #[test]
    fn test_search() {
        const TEST_FANOUT: usize = 2;
        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(0), Some(2)],
            records: vec![
                Arc::new(RwLock::new(Some(String::from("John")))),
                Arc::new(RwLock::new(Some(String::from("Adam")))),
            ],
            prev: Arc::downgrade(&Arc::new(RwLock::new(None))),
            next: Weak::new(),
        });
        let node_leaf1_ptr = Arc::new(RwLock::new(Some(node_leaf1)));

        // Create node (10 = "Emily"), (12 = "Jessica")
        let node_leaf2: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(10), Some(12)],
            records: vec![
                Arc::new(RwLock::new(Some(String::from("Emily")))),
                Arc::new(RwLock::new(Some(String::from("Jessica")))),
            ],
            prev: Arc::downgrade(&node_leaf1_ptr),
            next: Weak::new(),
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(Some(node_leaf2)));

        // Create node (20 = "Sam")
        let node_leaf3: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 1,
            keys: vec![Some(20), None],
            records: vec![
                Arc::new(RwLock::new(Some(String::from("Sam")))),
                Arc::new(RwLock::new(None)),
            ],
            prev: Arc::downgrade(&node_leaf2_ptr),
            next: Weak::new(),
        });
        let node_leaf3_ptr = Arc::new(RwLock::new(Some(node_leaf3)));

        // Set node_leaf1_ptr's ptr_leaf_next to node_leaf2_ptr
        let mut lock = node_leaf1_ptr.write();
        lock.as_mut().unwrap().get_leaf_mut().unwrap().next = Arc::downgrade(&node_leaf2_ptr);
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write();
        lock.as_mut().unwrap().get_leaf_mut().unwrap().next = Arc::downgrade(&node_leaf3_ptr);
        drop(lock);

        // Create interior (node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr)
        let node_interior1: Node<TEST_FANOUT, i32, String> = Node::Interior(Interior {
            num_keys: 2,
            keys: vec![Some(10), Some(20)],
            children: vec![node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr],
        });
        let node_interior1_ptr = Arc::new(RwLock::new(Some(node_interior1)));

        // Create B+Tree
        let bptree1: BPTree<TEST_FANOUT, i32, String> = BPTree {
            root: node_interior1_ptr,
        };

        let res = bptree1.search(&0).unwrap();
        let lock = res.read();
        assert_eq!(lock.as_ref().unwrap(), "John");
        drop(lock);

        let res = bptree1.search(&2).unwrap();
        let lock = res.read();
        assert_eq!(lock.as_ref().unwrap(), "Adam");
        drop(lock);

        let res = bptree1.search(&10).unwrap();
        let lock = res.read();
        assert_eq!(lock.as_ref().unwrap(), "Emily");
        drop(lock);

        let res = bptree1.search(&12).unwrap();
        let lock = res.read();
        assert_eq!(lock.as_ref().unwrap(), "Jessica");
        drop(lock);

        let res = bptree1.search(&20).unwrap();
        let lock = res.read();
        assert_eq!(lock.as_ref().unwrap(), "Sam");
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
    fn test_insert_simple() {
        let bptree = BPTree::<3, i32, i32>::new();

        bptree.insert(5, 2);

        let a = bptree.search(&5).unwrap();
        let lock = a.read();
        assert_eq!(*lock.as_ref().unwrap(), 2);
    }

    #[test]
    fn test_insert_simple_split() {
        let bptree = BPTree::<3, i32, i32>::new();

        bptree.insert(3, 5);
        bptree.insert(5, 3);
        // trigger split
        bptree.insert(7, 4);
    }

    #[test]
    fn test_range_search() {
        const TEST_FANOUT: usize = 2;

        // Create node (0 = "John"), (2 = "Adam")
        let node_leaf1: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(0), Some(2)],
            records: vec![
                Arc::new(RwLock::new(Some(String::from("John")))),
                Arc::new(RwLock::new(Some(String::from("Adam")))),
            ],
            prev: Weak::new(),
            next: Weak::new(),
        });
        let node_leaf1_ptr = Arc::new(RwLock::new(Some(node_leaf1)));

        // Create node (10 = "Emily"), (12 = "Jessica")
        let node_leaf2: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 2,
            keys: vec![Some(10), Some(12)],
            records: vec![
                Arc::new(RwLock::new(Some(String::from("Emily")))),
                Arc::new(RwLock::new(Some(String::from("Jessica")))),
            ],
            prev: Arc::downgrade(&node_leaf1_ptr),
            next: Weak::new(),
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(Some(node_leaf2)));

        // Create node (20 = "Sam")
        let node_leaf3: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 1,
            keys: vec![Some(20), None],
            records: vec![
                Arc::new(RwLock::new(Some(String::from("Sam")))),
                Arc::new(RwLock::new(None)),
            ],
            prev: Arc::downgrade(&node_leaf2_ptr),
            next: Weak::new(),
        });
        let node_leaf3_ptr = Arc::new(RwLock::new(Some(node_leaf3)));

        // Set node_leaf1_ptr's ptr_leaf_next to node_leaf2_ptr
        let mut lock = node_leaf1_ptr.write();
        lock.as_mut().unwrap().get_leaf_mut().unwrap().next = Arc::downgrade(&node_leaf2_ptr);
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write();
        lock.as_mut().unwrap().get_leaf_mut().unwrap().next = Arc::downgrade(&node_leaf3_ptr);
        drop(lock);

        // Create interior (node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr)
        let node_interior1: Node<TEST_FANOUT, i32, String> = Node::Interior(Interior {
            num_keys: 2,
            keys: vec![Some(10), Some(20)],
            children: vec![node_leaf1_ptr, node_leaf2_ptr, node_leaf3_ptr],
        });
        let node_interior1_ptr = Arc::new(RwLock::new(Some(node_interior1)));

        // Create B+Tree
        let bptree1: BPTree<TEST_FANOUT, i32, String> = BPTree {
            root: node_interior1_ptr,
        };

        let res = bptree1.search_range((&1, &2));
        let lock = res[0].read();
        assert_eq!(lock.as_ref().unwrap(), "Adam");
        drop(lock);

        let res = bptree1.search_range((&0, &2));
        let lock = res[0].read();
        assert_eq!(lock.as_ref().unwrap(), "John");
        drop(lock);
        let lock = res[1].read();
        assert_eq!(lock.as_ref().unwrap(), "Adam");
        drop(lock);

        let res = bptree1.search_range((&2, &12));
        let lock = res[0].read();
        assert_eq!(lock.as_ref().unwrap(), "Adam");
        drop(lock);
        let lock = res[1].read();
        assert_eq!(lock.as_ref().unwrap(), "Emily");
        drop(lock);
        let lock = res[2].read();
        assert_eq!(lock.as_ref().unwrap(), "Jessica");
        drop(lock);
    }
}
