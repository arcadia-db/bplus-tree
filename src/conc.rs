use std::{
    sync::{RwLock, RwLockReadGuard, RwLockWriteGuard, TryLockError, TryLockResult},
    thread::sleep,
    time::Duration,
};

use super::{node::*, typedefs::*};

pub struct SharedLatch<'a, const FANOUT: usize, K: Key, V: Record> {
    pub lock: RwLockReadGuard<'a, Node<FANOUT, K, V>>,
    pub node: NodePtr<FANOUT, K, V>,
}

pub struct ExclusiveLatch<'a, const FANOUT: usize, K: Key, V: Record> {
    pub lock: RwLockWriteGuard<'a, Node<FANOUT, K, V>>,
    pub node: NodePtr<FANOUT, K, V>,
}

pub trait TryLockOperation<T> {
    fn try_read_wait(&self) -> TryLockResult<RwLockReadGuard<'_, T>>;
    fn try_write_wait(&mut self) -> TryLockResult<RwLockWriteGuard<'_, T>>;
}

impl<T> TryLockOperation<T> for RwLock<T> {
    fn try_read_wait(&self) -> TryLockResult<RwLockReadGuard<'_, T>> {
        let mut current_lock_attempt = self.try_read();
        let mut attempts = 2;
        while let Err(TryLockError::WouldBlock) = current_lock_attempt {
            if attempts <= 0 {
                break;
            }
            sleep(Duration::from_nanos(50));
            current_lock_attempt = self.try_read();
            attempts -= 1;
        }
        current_lock_attempt
    }

    fn try_write_wait(&mut self) -> TryLockResult<RwLockWriteGuard<'_, T>> {
        let mut current_lock_attempt = self.try_write();
        let mut attempts = 2;
        while let Err(TryLockError::WouldBlock) = current_lock_attempt {
            if attempts <= 0 {
                break;
            }
            sleep(Duration::from_nanos(50));
            current_lock_attempt = self.try_write();
            attempts -= 1;
        }
        current_lock_attempt
    }
}
