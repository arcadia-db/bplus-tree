use parking_lot::RwLock;
use std::sync::Arc;

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
