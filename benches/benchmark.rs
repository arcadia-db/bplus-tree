use bplus_tree::bptree::BPTree;
use criterion::{criterion_group, criterion_main, Criterion};

use std::thread;

fn bench_read_heavy() {
    let bptree: BPTree<20000, i32, i32> = BPTree::new();
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
            }
        }),
        thread::spawn(move || {
            for i in 5000..15000 {
                let a = clone_2.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
            }
        }),
        thread::spawn(move || {
            for i in 10000..20000 {
                let a = clone_3.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
            }
        }),
        thread::spawn(move || {
            for i in 15000..25000 {
                let a = clone_4.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
            }
        }),
        thread::spawn(move || {
            for i in 5000..40000 {
                let a = clone_5.search(&i).unwrap();
                assert_eq!(a.read().unwrap(), i);
            }
        }),
    ];

    for handle in handles {
        handle.join().unwrap()
    }
}

fn bench_read_simple() {
    let bptree: BPTree<20000, i32, i32> = BPTree::new();

    for i in 0..50000 {
        bptree.insert(i, i);
    }

    let handles = [thread::spawn(move || {
        for i in 5000..40000 {
            let a = bptree.search(&i).unwrap();
            assert_eq!(a.read().unwrap(), i);
        }
    })];

    for handle in handles {
        handle.join().unwrap()
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("bptree-read-workload");
    group.sample_size(10);
    group.bench_function("read heavy 20000", |b| b.iter(bench_read_heavy));
    group.bench_function("read simple 20000", |b| b.iter(bench_read_simple));
    group.finish();
}

// fn read_lock() -> i32 {
//     let a = Arc::new(RwLock::new(5));
//     let mut res = 0;
//     for _i in 0..1000000 {
//         let b = a.read();
//         res += *b;
//     }
//     res
// }

// fn read() {
//     let a = 5;
//     let mut res = 0;
//     for _i in 0..1000000 {
//         let b = a;
//         res += black_box(b)
//     }
//     black_box(res);
// }

// fn write_lock() {
//     let a = Arc::new(RwLock::new(5));
//     for _i in 0..1000000 {
//         *a.write() = _i;
//     }
// }

// fn write() -> i32 {
//     let mut a = 5;
//     for _i in 0..1000000 {
//         a = black_box(_i);
//     }
//     return a;
// }

// fn rwlock_benchmark(c: &mut Criterion) {
//     let mut group = c.benchmark_group("rwlock-read-write");
//     group.bench_function("rwlock read 1M", |b| b.iter(|| read_lock()));
//     group.bench_function("var read 1M", |b| b.iter(|| read()));
//     group.bench_function("rwlock write 1M", |b| b.iter(|| write_lock()));
//     group.bench_function("var write 1M", |b| b.iter(|| write()));
//     group.sample_size(10000);
//     group.finish()
// }

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
