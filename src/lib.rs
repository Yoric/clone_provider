#![feature(const_fn)]
use std::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

/// A cell holding values protected by an atomic lock.
///
/// This cell is designed to hold values that implement `Clone` and to
/// distribute them to threads as needed. It may be instantiated as
/// a `static` value.
///
/// This cell is optimized for low contention.
///
/// FIXME: Resolve the matter of dropping.
///
/// FIXME: May need to poison the cell in case of panic in `clone`.
impl<T> AtomicCell<T> where T: Clone {
    ///
    /// Create an empty cell.
    ///
    pub const fn new() -> Self {
        AtomicCell {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
            lock: AtomicBool::new(true)
        }
    }

    ///
    /// Put a value in the cell.
    ///
    /// If there was a previous value, it is dropped.
    ///
    /// Argument `value` will **not** be dropped automatically. You should
    /// call `set`, `unset` or `swap` to ensure that it is dropped.
    ///
    /// See also `swap`.
    ///
    /// # Performance
    ///
    /// This method requires acquiring an atomic lock. If contention
    /// is low, it should be very fast. However, in case of high
    /// contention, performance may degrade considerably.
    ///
    pub fn set(&self, value: T) {
        self.swap(Some(Box::new(value)));
    }

    ///
    /// Remove whichever value is in the cell.
    ///
    /// If there was a previous value, it is dropped.
    ///
    /// Argument `value` will **not** be dropped automatically. You should
    /// call `set`, `unset` or `swap` to ensure that it is dropped.
    ///
    /// # Performance
    ///
    /// This method requires acquiring an atomic lock. If contention
    /// is low, it should be very fast. However, in case of high
    /// contention, performance may degrade considerably.
    ///
    pub fn unset(&self) {
        self.swap(None);
    }

    ///
    /// Get a clone of the current value in the cell.
    ///
    /// # Performance
    ///
    /// This method requires acquiring an atomic lock. If contention
    /// is low, it should be very fast. However, in case of high
    /// contention, performance may degrade considerably.
    ///
    /// # Panics
    ///
    /// If the `clone` method panics, this will cause a panic.
    ///
    /// FIXME: In the current state of things, a panic in the call to
    /// `clone` will also render the cell unusable forever (the lock
    /// can never be acquired).
    ///
    pub fn get(&self) -> Option<Box<T>> {
        self.with_lock(|| {
            let ptr = self.ptr.load(Ordering::Relaxed).clone();
            // The original. We must be very careful to not drop it.
            let original = self.opt_from_ptr(ptr);

            let result = original.clone(); // FIXME: What if this panics? Do we need poisoning?

            // Eat back `original` to ensure that it is not dropped.
            self.ptr_from_opt(original);
            result
        })
    }

    ///
    /// Replace the value currently in the cell with another value.
    ///
    /// # Performance
    ///
    /// This method requires acquiring an atomic lock. If contention
    /// is low, it should be very fast. However, in case of high
    /// contention, performance may degrade considerably.
    ///
    pub fn swap(&self, value: Option<Box<T>>) -> Option<Box<T>> {
        let new_ptr = self.ptr_from_opt(value);
        // We are now the owner of `value` as a pointer. From this
        // point, we are in charge of dropping it manually.
        self.with_lock(|| {
            let old_ptr = self.ptr.swap(new_ptr, Ordering::Relaxed);
            self.opt_from_ptr(old_ptr)
        })
    }

    fn ptr_from_opt(&self, value: Option<Box<T>>) -> *mut T {
        match value {
            None => std::ptr::null_mut(),
            Some(b) => Box::into_raw(b)
        }
    }

    fn opt_from_ptr(&self, ptr: *mut T) -> Option<Box<T>> {
        if ptr.is_null() {
            None
        } else {
            unsafe { Some(Box::from_raw(ptr)) }
        }
    }

    ///
    /// Acquire the lock.
    ///
    /// We use an atomic spinlock.
    ///
    /// # Safety
    ///
    /// If `f` panics, the lock becomes impossible to
    /// acquire. Ever. You have been warned.
    ///
    fn with_lock<F, R>(&self, f: F) -> R where F: FnOnce() -> R {
        loop {
            // Attempt to acquire the lock.
            // This data structure is designed for low contention, so we can use
            // an atomic spinlock.
            let owning = self.lock.compare_and_swap(/*must be available*/true,
                                                    /*mark as unavailable*/false, Ordering::Relaxed); // FIXME: Check ordering.
            if owning {
                // We are now the owner of the lock.
                // We must be very careful not to panic becore we have released the lock.
                let result = f();

                // Release the lock.
                self.lock.swap(true, Ordering::Relaxed);

                return result;
            }
        }
    }
}

pub struct AtomicCell<T> where T: Clone {
    ptr: AtomicPtr<T>,
    lock: AtomicBool
}

unsafe impl<T> Sync for AtomicCell<T> where T: Clone + Send {
}


#[cfg(test)]
mod test {
    use super::AtomicCell;

    use std::ops::Add;
    use std::sync::mpsc::{channel, Sender};
    use std::thread;

    // Test that we can allocate a cell and use it to distribute value
    // to several threads.
    static CELL: AtomicCell<Sender<u32>> = AtomicCell::new();
    #[test]
    fn test_channels() {
        let (tx, rx) = channel();
        CELL.set(tx);
        for i in 0..10 {
            thread::spawn(move || {
                let tx = CELL.get().unwrap();
                tx.send(i).unwrap();
            });
        }
        assert_eq!(rx.iter().take(10).fold(0, Add::add), 45);
    }

    // Test that `get()` on an empty cell returns `None`.
    static CELL2: AtomicCell<u32> = AtomicCell::new();
    #[test]
    fn test_empty() {
        for _ in 0..10 {
            thread::spawn(move || {
                assert_eq!(CELL2.get(), None);
            });
        }
        assert_eq!(CELL2.get(), None);
    }
}
