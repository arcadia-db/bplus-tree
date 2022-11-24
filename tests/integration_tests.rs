use parking_lot::RwLock;
use std::sync::Arc;

use bplus_tree::bptree::BPTree;

pub trait LockInClosure<T> {
    fn safe_read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R;

    fn safe_write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R;
}

impl<T> LockInClosure<T> for Option<Arc<RwLock<T>>> {
    fn safe_read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let lock = self.as_ref().unwrap().read();
        f(&*lock)
    }

    fn safe_write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut lock = self.as_ref().unwrap().write();
        f(&mut *lock)
    }
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
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![2, 4, 9, 15, 18],
    );

    assert_eq!(
        bptree
            .search_range((&18, &34))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![18, 19, 21, 34],
    );

    assert_eq!(
        bptree
            .search_range((&18, &18))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![18],
    );

    // search with start in tree and end not in tree
    assert_eq!(
        bptree
            .search_range((&2, &24))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![2, 4, 9, 15, 18, 19, 21],
    );

    assert_eq!(
        bptree
            .search_range((&18, &20))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![18, 19],
    );

    // search with start not in tree but end in tree
    assert_eq!(
        bptree
            .search_range((&5, &18))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![9, 15, 18],
    );

    assert_eq!(
        bptree
            .search_range((&0, &9))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![1, 2, 4, 9],
    );

    assert_eq!(
        bptree
            .search_range((&14, &34))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![15, 18, 19, 21, 34],
    );

    assert_eq!(
        bptree
            .search_range((&16, &21))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![18, 19, 21],
    );

    assert_eq!(
        bptree
            .search_range((&3, &15))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![4, 9, 15],
    );

    // search with both bounds not in tree
    assert_eq!(
        bptree
            .search_range((&16, &22))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![18, 19, 21],
    );

    assert_eq!(
        bptree
            .search_range((&35, &123))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![121],
    );

    assert_eq!(
        bptree
            .search_range((&3, &17))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![4, 9, 15],
    );

    assert_eq!(
        bptree
            .search_range((&20, &35))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![21, 34],
    );

    // search outside the range of the interval (empty)
    assert_eq!(
        bptree
            .search_range((&-5, &0))
            .iter()
            .map(|item| *item.try_read().unwrap())
            .collect::<Vec<i32>>(),
        vec![],
    );

    assert_eq!(
        bptree
            .search_range((&122, &156))
            .iter()
            .map(|item| *item.try_read().unwrap())
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
    let lock = res.read();
    assert_eq!(*lock, "Emily");
    drop(lock);

    let res = bptree.search(&5).unwrap();
    let lock = res.read();
    assert_eq!(*lock, "Srihari");
    drop(lock);

    // update value of 5
    bptree.insert(5, String::from("Cool"));
    let res = bptree.search(&5).unwrap();
    let lock = res.read();
    assert_eq!(*lock, "Cool");
    drop(lock);

    // this should trigger a leaf split, and create a new root node
    bptree.insert(7, String::from("Rajat"));
    let res = bptree.search(&7).unwrap();
    let lock = res.read();
    assert_eq!(*lock, "Rajat");
    drop(lock);

    bptree.insert(4, String::from("Erik"));
    let res = bptree.search(&4).unwrap();
    let lock = res.read();
    assert_eq!(*lock, "Erik");
    drop(lock);

    // This causes a new leaf node and adding a key to the root internal node
    // println!("{:#?}", bptree);
    bptree.insert(14, String::from("Golden"));
    let res = bptree.search(&14).unwrap();
    let lock = res.read();
    assert_eq!(*lock, "Golden");
    drop(lock);

    bptree.insert(16, String::from("Backpack"));
    let res = bptree.search(&16).unwrap();
    let lock = res.read();
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
    let lock = res.read();
    assert_eq!(*lock, "Golden");
    drop(lock);

    let res = bptree.search_range((&1, &4));

    let expected = ["Vishnu", "Rajat", "Patwari", "Golden"];

    for i in 0..res.len() {
        let lock = res[i].read();
        assert_eq!(expected[i], *lock);
        drop(lock);
    }
    // println!("{:#?}", bptree);
}

#[test]
fn test_insert_large() {
    let keys = vec![
        4, 56, 81, 71, 57, 62, 12, 91, 31, 58, 92, 37, 61, 11, 98, 75, 17, 35, 36, 23, 39, 95, 42,
        78, 38, 13, 30, 34, 84, 69, 54, 50, 99, 43, 2, 83, 28, 27, 19, 45, 32, 80, 3, 47, 90, 14,
        49, 67, 72, 25, 24, 52, 93, 51, 0, 44, 18, 86, 66, 10, 88, 6, 79, 48, 68, 26, 33, 21, 60,
        73, 41, 29, 87, 89, 97, 40, 94, 8, 20, 15, 1, 74, 59, 70, 96, 16, 22, 77, 53, 82, 85, 7, 5,
        55, 63, 46, 76, 64, 65, 9,
    ];

    let values = vec![
        99, 27, 34, 37, 23, 38, 47, 67, 45, 17, 3, 50, 5, 70, 3, 53, 26, 36, 69, 68, 56, 77, 49,
        37, 11, 16, 6, 16, 86, 30, 77, 3, 12, 31, 35, 76, 79, 9, 91, 47, 79, 91, 62, 91, 61, 80,
        29, 89, 89, 46, 18, 86, 26, 14, 98, 87, 92, 74, 4, 26, 29, 17, 76, 70, 10, 1, 75, 50, 20,
        50, 47, 15, 44, 30, 78, 3, 69, 22, 60, 88, 48, 32, 32, 73, 73, 16, 85, 50, 8, 24, 41, 87,
        78, 75, 60, 66, 5, 70, 94, 97,
    ];

    let expected = vec![
        98, 48, 35, 62, 99, 78, 17, 87, 22, 97, 26, 70, 47, 16, 80, 88, 16, 26, 92, 91, 60, 50, 85,
        68, 18, 46, 1, 9, 79, 15, 6, 45, 79, 75, 16, 36, 69, 50, 11, 56, 3, 47, 49, 31, 87, 47, 66,
        91, 70, 29, 3, 14, 86, 8, 77, 75, 27, 23, 17, 32, 20, 5, 38, 60, 70, 94, 4, 89, 10, 30, 73,
        37, 89, 50, 32, 53, 5, 50, 37, 76, 91, 34, 24, 76, 86, 41, 74, 44, 29, 30, 61, 67, 3, 26,
        69, 77, 73, 78, 3, 12,
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
    assert!(bptree.is_empty());

    bptree.insert(5, 5);
    bptree.insert(4, 4);
    bptree.remove(&4);
    assert!(bptree.search(&4).is_none());
    bptree.search(&5).safe_read(|val| assert_eq!(*val, 5));

    // root is full
    bptree.insert(4, 4);

    // trigger split
    bptree.insert(6, 6);
    // bptree
    //     .root
    //     .safe_read(|node| assert_eq!(node.get_interior().unwrap().num_keys, 1));
    bptree.remove(&6);
    assert!(bptree.search(&6).is_none());
    bptree.remove(&5);
    // bptree
    //     .root
    //     .safe_read(|node| assert_eq!(node.get_leaf().unwrap().num_keys, 1));
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
                bptree.search(&removal_order[j]).safe_read(|val| *val),
                removal_order[j]
            )
        }
    }
}

#[test]
fn test_remove_3() {
    let values: Vec<usize> = vec![
        59, 88, 83, 41, 76, 62, 72, 29, 74, 70, 23, 84, 51, 98, 73, 93, 66, 17, 16, 9, 35, 27, 13,
        40, 56, 77, 60, 90, 53, 42, 50, 92, 64, 4, 52, 39, 61, 21, 32, 45, 68, 20, 18, 6, 15, 34,
        31, 69, 82, 14, 3, 48, 71, 28, 54, 12, 46, 33, 19, 79, 7, 11, 80, 47, 25, 86, 43, 1, 78,
        36, 91, 26, 58, 8, 57, 87, 24, 67, 30, 65, 38, 99, 10, 75, 55, 22, 63, 95, 96, 97, 0, 37,
        89, 85, 5, 94, 44, 81, 2, 49,
    ];
    let mut bptree: BPTree<3, usize, usize> = BPTree::new();
    for value in &values {
        bptree.insert(*value, *value)
    }

    let removal_order = [
        52, 62, 40, 93, 89, 29, 74, 49, 79, 54, 11, 82, 84, 76, 87, 69, 48, 5, 66, 28, 31, 44, 73,
        22, 59, 12, 0, 24, 21, 7, 61, 2, 71, 6, 19, 17, 85, 33, 8, 42, 96, 88, 38, 67, 60, 9, 45,
        95, 94, 51, 4, 99, 37, 83, 15, 81, 50, 23, 57, 68, 53, 92, 26, 39, 34, 86, 10, 1, 90, 80,
        46, 27, 91, 97, 77, 75, 18, 30, 63, 78, 14, 43, 16, 32, 35, 72, 20, 64, 41, 47, 55, 58, 13,
        98, 70, 25, 56, 65, 36, 3,
    ];

    for i in 0..removal_order.len() {
        let removal = removal_order[i];
        bptree.remove(&removal);
        assert!(bptree.search(&removal).is_none());

        for j in i + 1..removal_order.len() {
            assert_eq!(
                bptree.search(&removal_order[j]).safe_read(|val| *val),
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
            read_from_insert_file(String::from("tests/golden/stress_test_insert_1.golden"));
        sizes_insert_helper(&keys, &values, &expected, false);
    }
    #[test]
    fn test_insert_stress_2() {
        let (keys, values, expected) =
            read_from_insert_file(String::from("tests/golden/stress_test_insert_2.golden"));
        sizes_insert_helper(&keys, &values, &expected, false);
    }
    #[test]
    fn test_insert_stress_3() {
        let (keys, values, expected) =
            read_from_insert_file(String::from("tests/golden/stress_test_insert_3.golden"));
        sizes_insert_helper(&keys, &values, &expected, false);
    }

    #[test]
    fn test_remove_stress_1() {
        let values =
            read_from_remove_file(String::from("tests/golden/stress_test_remove_1.golden"));

        sizes_remove_helper(&values, false);
        let a = &values[0..values.len() / 200];
        sizes_remove_helper(a, true);
    }

    #[test]
    fn test_remove_stress_2() {
        let values =
            read_from_remove_file(String::from("tests/golden/stress_test_remove_2.golden"));

        sizes_remove_helper(&values, false);
        let a = &values[0..values.len() / 200];
        sizes_remove_helper(a, true);
    }

    #[test]
    fn test_remove_stress_3() {
        let values =
            read_from_remove_file(String::from("tests/golden/stress_test_remove_3.golden"));

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
                    let lock = res.read();
                    assert_eq!(*lock, values[j]);
                    drop(lock);
                }
            }

            let res = bptree.search_range((&0, &(std::usize::MAX - 1)));
            assert_eq!(res.len(), expected.len());

            for i in 0..res.len() {
                let lock = res[i].read();
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
