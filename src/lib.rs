#![feature(const_fn)]
#![feature(catch_panic)] // For testing


use std::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

/// A cell holding values protected by an atomic lock.
///
/// This cell is designed to be instantiated as a global variable, to
/// hold a single value and to distribute it to threads as needed.  It
/// was initially designed to distribute clones of `Sender` to
/// hundreds of clients across dozens of modules without having to
/// pass these senders as argument through hundreds of intermediate
/// functions.
///
/// # Example
///
/// ```
/// #![feature(const_fn)]
/// use std::thread;
/// use std::sync::mpsc::{channel, Sender};
/// use std::ops::Add;
///
/// use atomic_cell::StaticCell;
///
/// // Sender cannot be defined as a `static` for two reasons:
/// // - it does not implement `Sync`;
/// // - it has a destructor.
/// // So let's implement it as a `StaticCell`.
/// static CELL: StaticCell<Sender<u32>> = StaticCell::new();
///
/// fn main() {
///   let (sender, receiver) = channel();
///   let _guard = CELL.init(sender);
///   // From this point and until `_guard` is dropped, `CELL` owns `sender`.
///
///   for i in 0..10 {
///     thread::spawn(move || {
///       // Any thread can now access clones of `sender`.
///       let sender = CELL.get().unwrap();
///       sender.send(i).unwrap();
///     });
///   }
///
///   // Make sure that all data was received properly.
///   assert_eq!(receiver.iter().take(10).fold(0, Add::add), 45);
///
///   // When we leave `main()`, `_guard` will go out of scope and
///   // will be dropped. This will cause `sender` to be dropped.
/// }
/// ```
///
///
/// # Performance
///
/// This cell is optimized for low contention. If there is no
/// contention, each call to `get` is resolved as a single atomic
/// read. In presence of high contention on a single cell, though,
/// performance may degrade considerably.
///
///
///
/// # Resource-safety
///
/// Unlike other kinds of static holders, values in `StaticCell` are
/// scoped and will be dropped, once the guard is dropped.
///
///
///
pub struct StaticCell<T> where T: Clone {
    internal: InternalAtomicCell<T>,
    initialized: AtomicBool
}

impl<T> StaticCell<T> where T: Clone {
    ///
    /// Create an empty cell.
    ///
    /// Call `init` to fill the cell.
    ///
    pub const fn new() -> Self {
        StaticCell {
            initialized: AtomicBool::new(false),
            internal: InternalAtomicCell::const_new()
        }
    }

    /// Initialize the cell.
    ///
    /// This methods returns a guard, which will drop `value` once it is dropped itself.
    /// Once this is done, `self` will return to being an empty cell. It will, however,
    /// remain initialized and cannot ever be initialized again.
    ///
    /// # Panics
    ///
    /// This method panicks if the cell is already initialized.
    pub fn init<'a>(&'a self, value: T) -> CleanGuard<'a> {
        let initialized = self.initialized.compare_and_swap(false, true, Ordering::Relaxed);
        if initialized {
            panic!("StaticCell is already initialized.");
        }
        self.internal.set(value);
        return CleanGuard {
            item: self
        }
    }

    /// Get a clone of the value held by the cell.
    ///
    /// Returns `None` if the cell is empty, either because it is not
    /// initialized or because the guard has been dropped.
    ///
    /// # Panics
    ///
    /// This method panicks if the call to `value.clone()` causes a
    /// panic.  However, the cell remains usable.
    pub fn get(&self) -> Option<Box<T>> {
        self.internal.get()
    }
}

trait CleanMeUp {
    fn clean(&self);
}

/// A guard used to drop the value held by a `StaticCell` at a
/// deterministic point in code.
///
/// Once the CleanGuard returned by `init()` is dropped, the value
/// held by the cell is also dropped.
pub struct CleanGuard<'a> {
    item: &'a CleanMeUp
}

impl<T> CleanMeUp for StaticCell<T> where T: Clone {
    ///
    /// Perform any cleanup.
    ///
    fn clean(&self) {
        self.internal.unset();
    }
}

impl<'a> Drop for CleanGuard<'a> {
    fn drop(&mut self) {
        self.item.clean();
    }
}

/// A cell holding values protected by an atomic lock.
///
/// This cell is designed to be instantiated as a local variable, to
/// hold a single value and to distribute it to threads as needed.
///
/// This cell cannot be allocated as a global variable. If you need a
/// global variable, use `StaticAtomicCell`.
///
///
/// # Performance
///
/// This cell is optimized for low contention. If there is no
/// contention, each call to `get` is resolved as a single atomic
/// read. In presence of high contention on a single cell, though,
/// performance may degrade considerably.
///
pub struct AtomicCell<T> where T: Clone {
    internal: InternalAtomicCell<T>
}

impl<T> AtomicCell<T> where T: Clone {
    ///
    /// Create a new empty cell.
    ///
    /// Use `set` or `swap` to add contents.
    ///
    pub fn new() -> Self {
        AtomicCell {
            internal: InternalAtomicCell::new()
        }
    }

    ///
    /// Set the contents of the cell.
    ///
    /// `value` will be dropped either when the cell is dropped, or
    /// when `set` is called once again. Property of `value` is
    /// transferred to the client if `swap` is called.
    ///
    /// If the cell already held some contents, drop these contents.
    ///
    pub fn set(&self, value: T) {
        self.internal.set(value)
    }

    /// Get a clone of the value held by the cell.
    ///
    /// Returns `None` if the cell is empty.
    ///
    /// # Panics
    ///
    /// A panic during the call to `value.clone()` will propagate and
    /// cause a panic in the cell.  However, the cell will remain
    /// usable.
    pub fn get(&self) -> Option<Box<T>> {
        self.internal.get()
    }

    ///
    /// Empty the cell manually.
    ///
    /// If the cell was empty, this is a noop. Otherwise, the previous
    /// value held is dropped.
    ///
    pub fn unset(&self) {
        self.internal.unset()
    }

    ///
    /// Swap the value held by the cell with a new value.
    ///
    pub fn swap(&self, value: Option<Box<T>>) -> Option<Box<T>> {
        self.internal.swap(value)
    }
}

impl<T> Drop for AtomicCell<T> where T: Clone {
    ///
    /// Drop any content present in the cell.
    ///
    fn drop(&mut self) {
        self.unset();
    }
}

/// A cell holding values protected by an atomic lock.
///
/// This cell is designed to hold values that implement `Clone` and to
/// distribute them to threads as needed. It may be instantiated as
/// a `static` value.
///
/// This cell is optimized for low contention.
///
/// This version does NOT guarantee that the values it holds are
/// dropped.
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
    use std::sync::atomic::{AtomicBool, Ordering};


    // Test that we can allocate a cell and use it to distribute value
    // to several threads.
    static CELL: StaticCell<Sender<u32>> = StaticCell::new();
    #[test]
    fn test_channels() {
        let (tx, rx) = channel();
        let _guard = CELL.init(tx);
        for i in 0..10 {
            thread::spawn(move || {
                let tx = CELL.get().unwrap();
                tx.send(i).unwrap();
            });
        }
        assert_eq!(rx.iter().take(10).fold(0, Add::add), 45);
    }

    // Test that `get()` on an empty cell returns `None`.
    static CELL2: StaticCell<u32> = StaticCell::new();
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
    static mut should_panic: AtomicBool = AtomicBool::new(true);
    struct Panicky;
    impl Clone for Panicky {
        fn clone(&self) -> Self {
            unsafe {
                if should_panic.load(Ordering::Relaxed) {
                    panic!("I have panicked, as expected");
                }
            }
            Panicky
        }
    }

    static CELL_PANIC: StaticCell<Panicky> = StaticCell::new();
    #[test]
    fn test_panic() {
        let original = Panicky;

        // First, cause a panic.
        let _guard = CELL_PANIC.init(original);
        let panic = thread::catch_panic(|| {
            CELL_PANIC.get() // Should panic
        });
        assert!(panic.is_err());

        // Now stop the panic.
        unsafe {
            should_panic.swap(false, Ordering::Relaxed);
        }

        // This shouldn't panic.
        CELL_PANIC.get().unwrap();
    }

    static CELL_INIT: StaticCell<u32> = StaticCell::new();
    #[test]
    fn test_init() {
        {
            let mut _guard = CELL_INIT.init(0);
            CELL_INIT.get().unwrap();
        }
        assert_eq!(CELL_INIT.get(), None);
    }
}
