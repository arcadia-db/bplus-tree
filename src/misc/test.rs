use std::sync::{Arc, RwLock};

pub enum Test {
    A { size: i32, a: [String; 2] },
    B,
}

pub fn ret() -> Arc<RwLock<Test>> {
    Arc::new(RwLock::new(Test::A {
        size: 32,
        a: ["a".into(), "b".into()],
    }))
}

pub fn test() -> Option<bool> {
    let r = ret();

    let mut lock = r.try_write().ok()?;
    match *lock {
        Test::A { size, ref mut a } => {
            println!("{:?}", size);
            a[0] = "c".into();
        }
        Test::B => {}
    }
    drop(lock);

    Some(true)
}
