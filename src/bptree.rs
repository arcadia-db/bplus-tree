use super::{conc::*, node::*, typedefs::*};
use parking_lot::RwLock;
use std::sync::Arc;
use std::time::Duration;
use std::{mem, vec};

#[derive(Debug)]
pub struct BPTree<const FANOUT: usize, K: Key, V: Record> {
    root: Option<NodePtr<FANOUT, K, V>>,
}

impl<const FANOUT: usize, K: Key, V: Record> BPTree<FANOUT, K, V> {
    pub fn new() -> Self {
        assert!(FANOUT > 1);
        Self { root: None }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn search(&self, key: &K) -> Option<RecordPtr<V>> {
        let leaf_traversal = Self::get_leaf_shared(self.root.clone(), key);
        leaf_traversal.as_ref()?;
        let lock = leaf_traversal.unwrap().lock;
        let leaf = lock.get_leaf().unwrap();
        for i in 0..leaf.num_keys {
            if *key == *leaf.keys[i].as_ref().unwrap() {
                return Some(leaf.records[i].as_ref().unwrap().clone());
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

            let traversal = Self::get_leaf_shared(self.root.clone(), start);
            // the only case the traversal is none is if the root node is None (empty tree)
            if traversal.is_none() {
                return result;
            }

            let latch = traversal.unwrap();
            let mut leaf = Some(latch.node);
            let mut leaf_lock = latch.lock;

            // Find position within leaf
            let mut leaf_node = leaf_lock.get_leaf().unwrap();

            let mut i = 0;
            while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() < start {
                i += 1;
            }

            // this loops through leaf nodes + records that fall in the given range
            loop {
                while i < leaf_node.num_keys && leaf_node.keys[i].as_ref().unwrap() <= end {
                    if leaf_node.keys[i].as_ref().unwrap() >= start {
                        result.push(leaf_node.records[i].as_ref().unwrap().clone());
                    }
                    i += 1;
                }
                if i != leaf_node.num_keys {
                    return result;
                }
                if let Some(node) = &leaf_node.next {
                    let _temp_node = leaf;
                    leaf = node.upgrade();
                    let _temp_lock = leaf_lock;

                    // attempt next result retrieval
                    let cur_lock_attempt = leaf
                        .as_ref()
                        .unwrap()
                        .try_upgradable_read_arc_for(Duration::from_nanos(50));
                    if let Some(guard) = cur_lock_attempt {
                        leaf_lock = guard;
                        leaf_node = leaf_lock.get_leaf().unwrap();
                    } else {
                        break;
                    }
                } else {
                    return result;
                }
                i = 0;
            }
        }
    }

    pub fn insert(&mut self, key: K, record: V) {
        // 1 - Empty tree so start a new tree
        if self.root.is_none() {
            let mut new_node = Node::new_leaf();
            new_node.keys[0] = Some(key);
            new_node.records[0] = Some(Arc::new(RwLock::new(record)));
            new_node.num_keys += 1;
            self.root = Some(Arc::new(RwLock::new(Node::Leaf(new_node))));
            return;
        }

        // optimistic latching
        let mut ancestor_latches =
            Self::get_leaf_optimistic(self.root.clone(), &key, |node| node.has_space_for_insert());
        let ExclusiveLatchInfo {
            lock: mut leaf_lock,
            node: leaf_node,
        } = ancestor_latches.pop().unwrap();

        // 2 - Insert into leaf, splitting if needed
        let leaf = leaf_lock.get_leaf_mut().unwrap();

        let mut insertion_idx = 0;
        while insertion_idx < leaf.num_keys && *leaf.keys[insertion_idx].as_ref().unwrap() < key {
            insertion_idx += 1
        }

        // if it exists, just update the record
        if insertion_idx < leaf.num_keys && *leaf.keys[insertion_idx].as_ref().unwrap() == key {
            leaf.records[insertion_idx] = Some(Arc::new(RwLock::new(record)));
            return;
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
            leaf.num_keys = split;

            let new_key = new_leaf.keys[0].clone().unwrap();
            new_leaf.prev = Some(Arc::downgrade(&leaf_node));
            new_leaf.next = leaf.next.clone();

            let new_leaf_node = Arc::new(RwLock::new(Node::Leaf(new_leaf)));
            leaf.next = Some(Arc::downgrade(&new_leaf_node));
            drop(leaf_lock);

            self.insert_into_parent(leaf_node, new_key, new_leaf_node, ancestor_latches);
        }
    }

    pub fn remove(&mut self, key: &K) {
        if self.is_empty() {
            return;
        }
        // optimistic latching
        let mut ancestor_latches =
            Self::get_leaf_optimistic(self.root.clone(), key, |node| node.has_space_for_removal());

        let ExclusiveLatchInfo {
            lock: mut leaf_lock,
            node: leaf_node,
        } = ancestor_latches.pop().unwrap();

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
        if Arc::ptr_eq(&leaf_node, self.root.as_ref().unwrap()) {
            if leaf.num_keys == 0 {
                self.root = None;
            }
            return;
        }

        if leaf.num_keys >= (FANOUT - 1) / 2 {
            return;
        }

        let ExclusiveLatchInfo {
            lock: mut parent_lock,
            node: parent_node,
        } = ancestor_latches.pop().unwrap();
        let parent = parent_lock.get_interior_mut().unwrap();

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
        let mut sibling_lock = sibling_node.write();
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
            first.num_keys += second.num_keys;
            first.next = second.next.clone();
            second.prev = None;

            let right_child = if i < parent.num_keys {
                sibling_node.clone()
            } else {
                leaf_node
            };
            drop(leaf_lock);
            drop(sibling_lock);

            ancestor_latches.push(ExclusiveLatchInfo {
                lock: parent_lock,
                node: parent_node,
            });
            self.remove_from_parent(&right_child, ancestor_latches);
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
        mut ancestor_latches: Vec<ExclusiveLatchInfo<FANOUT, K, V>>,
    ) {
        // 2 cases for insert into parent
        // 1 - No parent for left/right. We need to make a new root node if there is no parent
        if ancestor_latches.is_empty() {
            let mut new_node: Interior<FANOUT, K, V> = Node::new_interior();
            new_node.keys[0] = Some(key);
            new_node.children[0] = Some(left);
            new_node.children[1] = Some(right);
            new_node.num_keys = 1;
            self.root = Some(Arc::new(RwLock::new(Node::Interior(new_node))));
            return;
        }
        let ExclusiveLatchInfo {
            lock: mut parent_lock,
            node: parent_node,
        } = ancestor_latches.pop().unwrap();
        let parent = parent_lock.get_interior_mut().unwrap();

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
        parent.children[left_idx_in_parent + 1] = Some(right);
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
            let new_interior_node = Arc::new(RwLock::new(Node::Interior(new_interior)));
            drop(parent_lock);
            self.insert_into_parent(parent_node, pushed_key, new_interior_node, ancestor_latches);
        }
    }

    fn remove_from_parent(
        &mut self,
        right_child: &NodePtr<FANOUT, K, V>,
        mut ancestor_latches: Vec<ExclusiveLatchInfo<FANOUT, K, V>>,
    ) {
        let ExclusiveLatchInfo {
            lock: mut interior_lock,
            node: interior_node,
        } = ancestor_latches.pop().unwrap();

        let mut interior = interior_lock.get_interior_mut().unwrap();
        let mut right_child_idx = 0;
        while right_child_idx <= interior.num_keys
            && !Arc::ptr_eq(
                interior.children[right_child_idx].as_ref().unwrap(),
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
        if Arc::ptr_eq(&interior_node, self.root.as_ref().unwrap()) {
            if interior.num_keys == 0 {
                self.root = interior.children[0].clone();
            }
            return;
        }

        if interior.num_keys >= FANOUT / 2 {
            return;
        }

        let ExclusiveLatchInfo {
            lock: mut parent_lock,
            node: parent_node,
        } = ancestor_latches.pop().unwrap();
        let parent = parent_lock.get_interior_mut().unwrap();

        let mut i = 0;
        while i <= parent.num_keys
            && !Arc::ptr_eq(&interior_node, parent.children[i].as_ref().unwrap())
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

        // acquiring this lock is safe since the parent has a write lock
        let mut sibling_lock = sibling_node.write();
        let sibling = sibling_lock.get_interior_mut().unwrap();
        let (first, second) = if i < parent.num_keys {
            (interior, sibling)
        } else {
            (sibling, interior)
        };

        // we can borrow a key from one the other node
        if first.num_keys > FANOUT / 2 || second.num_keys > FANOUT / 2 {
            let replacement_key;
            // borrow from second (the interior node in question is predecessor)
            if first.num_keys < second.num_keys {
                first.keys[first.num_keys] = Some(discriminator_key.clone());
                mem::swap(
                    &mut first.children[first.num_keys + 1],
                    &mut second.children[0],
                );

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
                second.keys[0] = Some(discriminator_key.clone());
                mem::swap(&mut second.children[0], &mut first.children[first.num_keys]);

                first.num_keys -= 1;
                second.num_keys += 1;
                debug_assert!(first.num_keys > 0);
                debug_assert!(second.num_keys > 0);
            };

            // replace the key in parent
            for parent_key in &mut parent.keys {
                if *parent_key.as_ref().unwrap() == discriminator_key {
                    parent_key.replace(replacement_key.unwrap());
                    break;
                }
            }
        }
        // keys can fit into one node so let's merge
        else {
            first.keys[first.num_keys] = Some(discriminator_key);
            for j in 0..second.num_keys {
                mem::swap(&mut first.keys[j + first.num_keys + 1], &mut second.keys[j]);
            }
            for j in 0..second.num_keys + 1 {
                mem::swap(
                    &mut first.children[j + first.num_keys + 1],
                    &mut second.children[j],
                );
            }

            let right_child = if i < parent.num_keys {
                sibling_node.clone()
            } else {
                interior_node
            };
            first.num_keys = first.num_keys + second.num_keys + 1;
            drop(sibling_lock);
            drop(interior_lock);
            ancestor_latches.push(ExclusiveLatchInfo {
                lock: parent_lock,
                node: parent_node,
            });
            self.remove_from_parent(&right_child, ancestor_latches);
        }
    }

    /* private */
    fn get_leaf_shared(
        root: Option<NodePtr<FANOUT, K, V>>,
        key: &K,
    ) -> Option<SharedLatchInfo<FANOUT, K, V>> {
        root.as_ref()?;
        let mut current_node = root.unwrap();
        let mut lock = current_node.upgradable_read_arc();

        while lock.is_interior() {
            current_node = {
                let mut i = 0;
                let node = lock.get_interior().unwrap();
                while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
                    i += 1;
                }
                node.children[i].clone().unwrap()
            };

            let _old_lock = lock;
            lock = current_node.upgradable_read_arc();
        }
        Some(SharedLatchInfo {
            node: current_node,
            lock,
        })
    }

    fn get_leaf_exclusive<F>(
        root: Option<NodePtr<FANOUT, K, V>>,
        key: &K,
        clear_ancestors_latches: F,
    ) -> Vec<ExclusiveLatchInfo<FANOUT, K, V>>
    where
        F: Fn(&Node<FANOUT, K, V>) -> bool,
    {
        if root.is_none() {
            return Vec::new();
        }
        let mut current_node = root.unwrap();
        let mut lock = current_node.write_arc();
        let mut latches: Vec<ExclusiveLatchInfo<FANOUT, K, V>> = Vec::new();

        while lock.is_interior() {
            let old_node = current_node;
            current_node = {
                let mut i = 0;
                let node = lock.get_interior().unwrap();
                while i < node.num_keys && *key >= *node.keys[i].as_ref().unwrap() {
                    i += 1;
                }
                node.children[i].as_ref().unwrap().clone()
            };

            latches.push(ExclusiveLatchInfo {
                lock,
                node: old_node,
            });

            lock = current_node.write_arc();

            // if we are sure that this node will not undergo any
            // structural changes, we can release the latches on all ancestors
            // if for_removal && lock.has_space_for_removal()
            //     || !for_removal && lock.has_space_for_insert()
            if clear_ancestors_latches(&lock) {
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
        root: Option<NodePtr<FANOUT, K, V>>,
        key: &K,
        clear_ancestors_latches: F,
    ) -> Vec<ExclusiveLatchInfo<FANOUT, K, V>>
    where
        F: Fn(&Node<FANOUT, K, V>) -> bool,
    {
        let leaf_traversal_optimistic = Self::get_leaf_shared(root.clone(), key);
        let leaf = leaf_traversal_optimistic.as_ref().unwrap();
        // we are safe from splitting so optimistic was good, and we upgrade to write latch
        if clear_ancestors_latches(&leaf.lock) {
            let leaf_shared_latch = leaf_traversal_optimistic.unwrap();
            vec![SharedLatchInfo::upgrade(leaf_shared_latch)]
        }
        // if the leaf will require a split / merge, so restart with exclusive
        else {
            drop(leaf_traversal_optimistic);
            Self::get_leaf_exclusive(root, key, clear_ancestors_latches)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

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
            prev: Some(Arc::downgrade(&node_leaf1_ptr)),
            next: None,
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(node_leaf2));

        // Create node (20 = "Sam")
        let node_leaf3: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 1,
            keys: vec![Some(20), None],
            records: vec![Some(Arc::new(RwLock::new(String::from("Sam")))), None],
            prev: Some(Arc::downgrade(&node_leaf2_ptr)),
            next: None,
        });
        let node_leaf3_ptr = Arc::new(RwLock::new(node_leaf3));

        // Set node_leaf1_ptr's ptr_leaf_next to node_leaf2_ptr
        let mut lock = node_leaf1_ptr.write();
        lock.get_leaf_mut().unwrap().next = Some(Arc::downgrade(&node_leaf2_ptr));
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write();
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
        });
        let node_interior1_ptr = Arc::new(RwLock::new(node_interior1));

        // Create B+Tree
        let bptree1: BPTree<TEST_FANOUT, i32, String> = BPTree {
            root: Some(node_interior1_ptr),
        };

        let res = bptree1.search(&0).unwrap();
        let lock = res.read();
        assert_eq!(*lock, "John");
        drop(lock);

        let res = bptree1.search(&2).unwrap();
        let lock = res.read();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search(&10).unwrap();
        let lock = res.read();
        assert_eq!(*lock, "Emily");
        drop(lock);

        let res = bptree1.search(&12).unwrap();
        let lock = res.read();
        assert_eq!(*lock, "Jessica");
        drop(lock);

        let res = bptree1.search(&20).unwrap();
        let lock = res.read();
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
            prev: Some(Arc::downgrade(&node_leaf1_ptr)),
            next: None,
        });
        let node_leaf2_ptr = Arc::new(RwLock::new(node_leaf2));

        // Create node (20 = "Sam")
        let node_leaf3: Node<TEST_FANOUT, i32, String> = Node::Leaf(Leaf {
            num_keys: 1,
            keys: vec![Some(20), None],
            records: vec![Some(Arc::new(RwLock::new(String::from("Sam")))), None],
            prev: Some(Arc::downgrade(&node_leaf2_ptr)),
            next: None,
        });
        let node_leaf3_ptr = Arc::new(RwLock::new(node_leaf3));

        // Set node_leaf1_ptr's ptr_leaf_next to node_leaf2_ptr
        let mut lock = node_leaf1_ptr.write();
        lock.get_leaf_mut().unwrap().next = Some(Arc::downgrade(&node_leaf2_ptr));
        drop(lock);

        // Set node_leaf2_ptr's ptr_leaf_next to node_leaf3_ptr
        let mut lock = node_leaf2_ptr.write();
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
        });
        let node_interior1_ptr = Arc::new(RwLock::new(node_interior1));

        // Create B+Tree
        let bptree1: BPTree<TEST_FANOUT, i32, String> = BPTree {
            root: Some(node_interior1_ptr),
        };

        let res = bptree1.search_range((&1, &2));
        let lock = res[0].read();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range((&0, &2));
        let lock = res[0].read();
        assert_eq!(*lock, "John");
        drop(lock);
        let lock = res[1].read();
        assert_eq!(*lock, "Adam");
        drop(lock);

        let res = bptree1.search_range((&2, &12));
        let lock = res[0].read();
        assert_eq!(*lock, "Adam");
        drop(lock);
        let lock = res[1].read();
        assert_eq!(*lock, "Emily");
        drop(lock);
        let lock = res[2].read();
        assert_eq!(*lock, "Jessica");
        drop(lock);
    }
}
