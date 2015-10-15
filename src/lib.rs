#![feature(const_fn)]
#![feature(catch_panic)] // For testing


use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::RefCell;

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
/// contention, each call to `get` is resolved as a single
/// (sequentially consistant) atomic read. In presence of high
/// contention on a single cell, though, performance may degrade
/// considerably.
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
    internal: RefCell<InternalAtomicCell<T>>,
    initialized: AtomicBool
}

unsafe impl<T> Sync for StaticCell<T> where T: Clone {
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
            internal: RefCell::new(InternalAtomicCell::const_new())
        }
    }

    /// Initialize the cell.
    ///
    /// This methods returns a guard, which will drop `value` once it
    /// is dropped itself.  Once this is done, `self` will return to
    /// being an empty cell. It will, however, remain initialized and
    /// cannot ever be initialized again.
    ///
    /// # Panics
    ///
    /// This method panicks if the cell is already initialized, or if
    /// initialization is racing with a call to `get`.
    pub fn init<'a>(&'a self, value: T) -> CleanGuard<'a> {
        let initialized = self.initialized.compare_and_swap(/* must be */false,
                                                            /* becomes */true,
                                                            Ordering::SeqCst);
        if initialized {
            panic!("StaticCell is already initialized.");
        }
        {
            self.internal.borrow_mut().set(value);
        }
        return CleanGuard::new(self)
    }

    /// Get a clone of the value held by the cell.
    ///
    /// Returns `None` if the cell is empty, either because it is not
    /// initialized or because the guard has been dropped.
    ///
    /// Receiving `None` is almost always a programming error, so
    /// client code is encouraged to `unwrap()` immediately.
    ///
    ///
    /// # Performance
    ///
    /// This methods uses an atomic spinlock. With low contention, it
    /// is generally quite fast (assuming that `clone()` is itself
    /// fast). In case of high contention, performance may degrade
    /// considerably. In case of doubt, ou may wish to ensure that
    /// your code calls `clone()` before entering a
    /// perfirmance-critical or high-contention section.
    ///
    ///
    /// # Panics
    ///
    /// This method panicks if the call to `value.clone()` causes a
    /// panic.  However, the cell remains usable.
    ///
    /// This method may panick if it is racing with `init()`. Just
    /// make sure that initialization is complete before using this
    /// cell, right?
    pub fn get(&self) -> Option<Box<T>> {
        self.internal.borrow().get()
    }
}

impl<T> CleanMeUp for StaticCell<T> where T: Clone {
    /// Drop the value currently held by the cell, if any.
    ///
    /// This method is called when the `CleanGuard` is dropped.
    fn clean(&self) {
        self.internal.borrow_mut().unset();
    }
}

/// An object that needs to be cleaned up.
pub trait CleanMeUp {
    /// Perform cleanup.
    fn clean(&self);
}


/// A guard used to drop the value held by a `CleanMeUp` at a
/// deterministic point in code. This is designed as an alternative to
/// `Drop` for global variables.
///
/// Once the `CleanGuard`, the value held by the cell is also dropped.
pub struct CleanGuard<'a> {
    item: &'a CleanMeUp
}

impl<'a> CleanGuard<'a> {
    /// Create a new guard in charge of cleaning up an object.
    ///
    /// Once the CleanGuard is dropped, the object's `clean` method is
    /// called.
    pub fn new(item: &'a CleanMeUp) -> Self {
        CleanGuard {
            item: item
        }
    }
}


impl<'a> Drop for CleanGuard<'a> {
    ///
    /// Call the guarded object's `clean` method.
    ///
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
/// contention, each call to `get` is resolved as a single
/// (sequentially consistent) atomic read. In presence of high
/// contention on a single cell, though, performance may degrade
/// considerably.
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
    pub fn set(&mut self, value: T) {
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
    pub fn unset(&mut self) {
        self.internal.unset()
    }

    ///
    /// Swap the value held by the cell with a new value.
    ///
    pub fn swap(&mut self, value: Option<Box<T>>) -> Option<Box<T>> {
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
            ptr: std::ptr::null_mut(),
            lock: AtomicBool::new(true),
        }
    }
    pub fn new() -> Self {
        InternalAtomicCell {
            ptr: std::ptr::null_mut(),
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
    pub fn set(&mut self, value: T) {
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
    pub fn unset(&mut self) {
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
        let maybe_clone = self.with_lock(|| {
            if self.ptr.is_null() {
                return None;
            }

            // Don't cast back to Box, as this would cause us to
            // `drop` the value in case of panic.
            Some(unsafe { (*self.ptr).clone() })
            // If `clone` panics, `with_lock` will ensure that the
            // lock is released.
        });
        // Allocate out of the lock.
        match maybe_clone {
            None => None,
            Some(clone) => Some(Box::new(clone))
        }
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
    pub fn swap(&mut self, value: Option<Box<T>>) -> Option<Box<T>> {
        let new_ptr = ptr_from_opt(value);
        // We are now the owner of `value` as a pointer. From this
        // point, we are in charge of dropping it manually.
        let old_ptr = self.with_lock_mut(|mut ptr : &mut*mut T| {
            let old_ptr = *ptr;
            *ptr = new_ptr;
            old_ptr
        });
        opt_from_ptr(old_ptr)
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
                                                    /*mark as unavailable*/false,
                                                    Ordering::Acquire);
            if owning {
                // We are now the owner of the lock.

                // Make sure that we eventually release the lock.
                let _guard = GuardLock::new(&self.lock);

                let result = f();

                return result;
            }
        }
    }
    fn with_lock_mut<F, R>(&mut self, f: F) -> R where F: FnOnce(&mut*mut T) -> R {
        loop {
            // Attempt to acquire the lock.
            // This data structure is designed for low contention, so we can use
            // an atomic spinlock.
            let owning = self.lock.compare_and_swap(/*must be available*/true,
                                                    /*mark as unavailable*/false,
                                                    Ordering::Acquire);
            if owning {
                // We are now the owner of the lock.

                // Make sure that we eventually release the lock.
                let _guard = GuardLock::new(&self.lock);

                let result = f(&mut self.ptr);

                return result;
            }
        }
    }

}

fn ptr_from_opt<T>(value: Option<Box<T>>) -> *mut T {
    match value {
        None => std::ptr::null_mut(),
        Some(b) => Box::into_raw(b)
    }
}

fn opt_from_ptr<T>(ptr: *mut T) -> Option<Box<T>> {
    if ptr.is_null() {
        None
    } else {
        unsafe { Some(Box::from_raw(ptr)) }
    }
}

struct InternalAtomicCell<T> where T: Clone {
    ///
    /// Pointer to the value held by the cell.
    ///
    /// This pointer may be `null`.
    ///
    ptr: *mut T,

    /// An atomic bool supporting a spinlock.
    ///
    /// If `true`, the lock can be acquired. If `false`, the lock
    /// is not available.
    lock: AtomicBool,
}

unsafe impl<T> Sync for InternalAtomicCell<T> where T: Clone + Send {
}

/// A guard used to ensure that we release a lock, even in case of
/// panic.
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
        self.lock.swap(true, Ordering::Release);
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
    static mut should_panic: AtomicBool = AtomicBool::new(false);
    struct Panicky {
        foo: u32
    }
    impl Clone for Panicky {
        fn clone(&self) -> Self {
            unsafe {
                if should_panic.load(Ordering::Relaxed) {
                    panic!("I have panicked, as expected");
                }
            }
            Panicky {
                foo: self.foo
            }
        }
    }

    static CELL_PANIC: StaticCell<Panicky> = StaticCell::new();
    #[test]
    fn test_panic() {
        let original = Panicky { foo: 500 };
        let _guard = CELL_PANIC.init(original.clone());

        // Now, cause a panic.
        unsafe {
            should_panic.swap(true, Ordering::Relaxed);
        }
        let panic = thread::catch_panic(|| {
            // This should panic.
            CELL_PANIC.get()
        });
        assert!(panic.is_err());

        // Now stop the panic.
        unsafe {
            should_panic.swap(false, Ordering::Relaxed);
        }

        // This shouldn't panic. Moreover, we should find
        // our original value.
        let result = CELL_PANIC.get().unwrap();
        assert_eq!(result.foo, original.foo);
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
