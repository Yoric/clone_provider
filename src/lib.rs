#![feature(const_fn)]
#![feature(catch_panic)] // For testing


use std::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

pub struct Global;
pub struct Scoped;

pub struct StaticAtomicCell<T> where T: Clone {
    internal: InternalAtomicCell<T>
}

impl<T> StaticAtomicCell<T> where T: Clone {
    pub const fn new() -> Self {
        StaticAtomicCell {
            internal: InternalAtomicCell::const_new()
        }
    }

    pub fn set(&self, value: T) {
        self.internal.set(value)
    }

    pub fn get(&self) -> Option<Box<T>> {
        self.internal.get()
    }

    pub fn unset(&self) {
        self.internal.unset()
    }

    pub fn swap(&self, value: Option<Box<T>>) -> Option<Box<T>> {
        self.internal.swap(value)
    }
}

pub struct AtomicCell<T> where T: Clone {
    internal: InternalAtomicCell<T>
}

impl<T> AtomicCell<T> where T: Clone {
    pub fn new() -> Self {
        AtomicCell {
            internal: InternalAtomicCell::new()
        }
    }

    pub fn set(&self, value: T) {
        self.internal.set(value)
    }

    pub fn get(&self) -> Option<Box<T>> {
        self.internal.get()
    }

    pub fn unset(&self) {
        self.internal.unset()
    }

    pub fn swap(&self, value: Option<Box<T>>) -> Option<Box<T>> {
        self.internal.swap(value)
    }
}

impl<T> Drop for AtomicCell<T> where T: Clone {
    fn drop(&mut self) {
        self.unset();
    }
}

/*
pub type AtomicCell<T> = InternalAtomicCell<Scoped, T>;

impl<T> AtomicCell<T> where T: Clone {
    pub fn new() -> Self {
        AtomicCell::internal_new()
    }
}
*/

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
impl<T> InternalAtomicCell<T> where T: Clone {
    ///
    /// Create an empty cell.
    ///
    pub const fn const_new() -> Self {
        InternalAtomicCell {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
            lock: AtomicBool::new(true),
        }
    }
    pub fn new() -> Self {
        InternalAtomicCell {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
            lock: AtomicBool::new(true),
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
    /// If the `clone` method panics, this will cause a panic. The cell
    /// will, however, remain usable.
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
    /// # Panics
    ///
    /// If `f` panics.
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

                // Make sure that we eventually release the lock.
                let _guard = GuardLock::new(&self.lock);

                let result = f();

                return result;
            }
        }
    }
}

struct InternalAtomicCell<T> where T: Clone {
    ptr: AtomicPtr<T>,
    lock: AtomicBool,
}

unsafe impl<T> Sync for InternalAtomicCell<T> where T: Clone + Send {
}

struct GuardLock<'a> {
    lock: &'a AtomicBool
}
impl<'a> GuardLock<'a> {
    fn new(lock: &AtomicBool) -> GuardLock {
        GuardLock {
            lock: lock
        }
    }
}
impl<'a> Drop for GuardLock<'a> {
    fn drop(&mut self) {
        self.lock.swap(true, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod test {
    use super::*;


    use std::ops::Add;
    use std::sync::mpsc::{channel, Sender};
    use std::thread;

    // Test that we can allocate a cell and use it to distribute value
    // to several threads.
    static CELL: StaticAtomicCell<Sender<u32>> = StaticAtomicCell::new();
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
    static CELL2: StaticAtomicCell<u32> = StaticAtomicCell::new();
    #[test]
    fn test_empty() {
        for _ in 0..10 {
            thread::spawn(move || {
                assert_eq!(CELL2.get(), None);
            });
        }
        assert_eq!(CELL2.get(), None);
    }

    // Test that a panic does not make the cell unusable.
    struct Panicky {
        pub should_panic: bool
    }
    impl Clone for Panicky {
        fn clone(&self) -> Self {
            if self.should_panic {
                panic!("I have panicked, as expected");
            }
            Panicky {
                should_panic: self.should_panic
            }
        }
    }

    static CELL_PANIC: StaticAtomicCell<Panicky> = StaticAtomicCell::new();
    #[test]
    fn test_panic() {
        // First, cause a panic.
        CELL_PANIC.set(Panicky { should_panic: true });
        let panic = thread::catch_panic(|| {
            CELL_PANIC.get() // Should panic
        });
        assert!(panic.is_err());

        // Now proceed, as if nothing had happened.
        CELL_PANIC.set(Panicky { should_panic: false });

        // This shouldn't panic.
        CELL_PANIC.get().unwrap();
    }

}
