use std::{thread, time::Duration};

use bplus_tree::bptree::BPTree;

mod common;

#[test]
fn test_write_heavy() {
    let bptree: BPTree<5, i32, i32> = BPTree::new();
    let clone_1 = bptree.clone();
    let clone_2 = bptree.clone();
    let clone_3 = bptree.clone();
    let clone_4 = bptree.clone();
    let clone_5 = bptree.clone();

    let handles = [
        thread::spawn(move || {
            for i in 0..10000 {
                clone_1.insert(i, i);
                thread::sleep(Duration::from_micros(10));
            }
        }),
        thread::spawn(move || {
            for i in 10000..20000 {
                clone_2.insert(i, i);
                thread::sleep(Duration::from_micros(15));
            }
        }),
        thread::spawn(move || {
            for i in 20000..30000 {
                clone_3.insert(i, i);
                thread::sleep(Duration::from_micros(12));
            }
        }),
        thread::spawn(move || {
            for i in 30000..40000 {
                clone_4.insert(i, i);
                thread::sleep(Duration::from_micros(18));
            }
        }),
        thread::spawn(move || {
            for i in 40000..50000 {
                clone_5.insert(i, i);
                thread::sleep(Duration::from_micros(11));
            }
        }),
    ];

    for handle in handles {
        handle.join().unwrap()
    }

    for i in 0..50000 {
        let a = bptree.search(&i).unwrap();
        assert_eq!(a.read().unwrap(), i);
    }
}

#[test]
fn test_read_heavy() {
    let bptree: BPTree<5, i32, i32> = BPTree::new();
    let clone_1 = bptree.clone();
    let clone_2 = bptree.clone();
    let clone_3 = bptree.clone();
    let clone_4 = bptree.clone();
    let clone_5 = bptree;

    for i in 0..50000 {
        clone_1.insert(i, i);
    }

    let handles = [
        thread::spawn(move || {
            for i in 0..10000 {
                let a = clone_1.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
                thread::sleep(Duration::from_micros(10));
            }
        }),
        thread::spawn(move || {
            for i in 5000..15000 {
                let a = clone_2.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
                thread::sleep(Duration::from_micros(15));
            }
        }),
        thread::spawn(move || {
            for i in 10000..20000 {
                let a = clone_3.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
                thread::sleep(Duration::from_micros(12));
            }
        }),
        thread::spawn(move || {
            for i in 15000..25000 {
                let a = clone_4.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
                thread::sleep(Duration::from_micros(18));
            }
        }),
        thread::spawn(move || {
            for i in 5000..40000 {
                let a = clone_5.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
                thread::sleep(Duration::from_micros(11));
            }
        }),
    ];

    for handle in handles {
        handle.join().unwrap()
    }
}

#[test]
fn test_mixed_workload() {
    let bptree: BPTree<5, i32, i32> = BPTree::new();
    let clone_1 = bptree.clone();
    let clone_2 = bptree.clone();
    let clone_3 = bptree.clone();
    let clone_4 = bptree.clone();
    let clone_5 = bptree.clone();

    let clone_6 = bptree.clone();
    let clone_7 = bptree.clone();
    let clone_8 = bptree.clone();
    let clone_9 = bptree.clone();
    let clone_10 = bptree;

    for i in 0..10000 {
        clone_1.insert(i, i);
    }

    let handles = [
        thread::spawn(move || {
            for i in 0..10000 {
                clone_1.search(&i);
            }
        }),
        thread::spawn(move || {
            for i in 5000..15000 {
                clone_2.insert(i, i);
            }

            for i in 10000..15000 {
                clone_2.remove(&i);
            }
        }),
        thread::spawn(move || {
            for i in 10000..20000 {
                clone_3.search(&i);
            }
            for i in 10000..15000 {
                clone_3.remove(&i);
            }
        }),
        thread::spawn(move || {
            clone_4.search_range((&15000, &2000));
            clone_4.search_range((&0, &20000));
            for i in 5000..15000 {
                clone_4.insert(i, i);
            }
            clone_4.search_range((&500, &10000));
            clone_4.search_range((&2000, &15000));
            for i in 5000..10000 {
                clone_4.remove(&i);
            }
        }),
        thread::spawn(move || {
            for i in 0..2000 {
                clone_5.insert(i, i);
            }

            for i in 6000..14000 {
                clone_5.remove(&i);
            }
            clone_5.search_range((&500, &1500));
        }),
        thread::spawn(move || {
            for i in 0..2000 {
                clone_6.insert(i, i);
            }
        }),
        thread::spawn(move || {
            for i in 20000..30000 {
                clone_7.insert(i, i);
            }
        }),
        thread::spawn(move || {
            for i in 5000..40000 {
                clone_8.search(&i);
            }
        }),
        thread::spawn(move || {
            for i in 2000..10000 {
                clone_9.search(&i);
            }
        }),
        thread::spawn(move || {
            for i in 3000..20000 {
                clone_10.search(&i);
            }
        }),
    ];

    for handle in handles {
        handle.join().unwrap()
    }
}
