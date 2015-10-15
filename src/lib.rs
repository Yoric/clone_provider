#![feature(const_fn)]
use std::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

/// A cell holding values protected by an atomic lock.
///
/// This cell is designed to hold values that implement `Clone` and to
/// distribute them to threads as needed. It may be instantiated as
/// a `static` value.
///
/// This cell is optimized for low contention.
impl<T> AtomicCell<T> where T: Clone {
    pub const fn new() -> Self {
        AtomicCell {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
            lock: AtomicBool::new(true)
        }
    }

    pub fn set(&self, value: T) {
        self.swap(Some(Box::new(value)));
    }

    pub fn unset(&self) {
        self.swap(None);
    }

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

    fn with_lock<F, R>(&self, f: F) -> R where F: FnOnce(/*&mut AtomicCell<T>*/) -> R {
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

    #[test]
    fn test_empty() {
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

}
