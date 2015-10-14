use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;

pub trait SyncClone: Clone {
}

/// A structure whose sole role is to provide clones of a source object to any thread that
/// requests it.
///
/// Initially, any call to `get` will return `None`. To let the `CloneProvider` provide
/// something more useful, clients need to call method `attach`.
impl<T> CloneProvider<T> where T: SyncClone {
    /// Provide an original for the `CloneProvider`, returns a guard.
    ///
    /// Until the guard is dropped, any call to `get` will return a
    /// clone of `value`. Once the guard is dropped, `value` is
    /// dropped and further calls to `get` will again return `None`.
    ///
    ///
    /// # Panics
    ///
    /// Calling attach again before dropping the guard will panic.
    pub fn attach(&self, value: Box<T>) -> Guard<T> {
        let ptr_new = Box::into_raw(value);
        let guard = Guard::new(self.current.clone(), ptr_new.clone());

        // Get rid of the original, if any.
        let ptr_old = self.current.swap(ptr_new.clone(), Ordering::Relaxed);
        if !ptr_old.is_null() {
            // The old pointer will now be dropped.
            unsafe {
                Box::from_raw(ptr_old);
            }
        }

        guard
    }

    /// Return a clone of the attached value.
    ///
    /// If there is no currently attached value, return `None`.
    pub fn get(&self) -> Option<Box<T>> {
        let ptr = self.current.load(Ordering::Relaxed);
        if ptr.is_null() {
            None
        } else {
            unsafe {
                let as_box = Box::from_raw(ptr);
                // Call clone, as advertised.
                let clone = as_box.clone();
                // Make sure that we do not drop the original box.
                Box::into_raw(as_box);
                Some(clone)
            }
        }
    }
}

impl<T> CloneProvider<T> where T: SyncClone {
  pub fn new() -> CloneProvider<T> {
    CloneProvider {
      current: Arc::new(AtomicPtr::new(std::ptr::null_mut()))
    }
  }
}

pub struct CloneProvider<T> where T: SyncClone {
    current: Arc<AtomicPtr<T>>
}

impl<T> Guard<T> where T: SyncClone {
    fn new(store: Arc<AtomicPtr<T>>, ptr: *mut T) -> Guard<T> {
        Guard {
            ptr: ptr,
            store: store
        }
    }
}

pub struct Guard<T> where T: SyncClone {
    ptr: *mut T,
    store: Arc<AtomicPtr<T>>
}
impl<T> Drop for Guard<T> where T: SyncClone {
    fn drop(&mut self) {
        let ptr_in_store =
            self.store.compare_and_swap(self.ptr,
                                        std::ptr::null_mut(), Ordering::Relaxed);
        if ptr_in_store == self.ptr {
            // We're the owner.
            unsafe {
                drop(Box::from_raw(ptr_in_store))
            }
        }
    }
}

unsafe impl<T> Sync for CloneProvider<T> where T: SyncClone {
}

