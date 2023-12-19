use prusti_contracts::*;

/// The API of this module is sound, in that it cannot be exploited by safe
/// code to cause UB.
mod lib {
    use std::sync::Mutex;
    use prusti_contracts::*;

    #[repr(C)]
    pub struct T<'a> {
        inner: &'a mut u32,
        mutex: Mutex<()>,
    }

    impl<'a> T<'a> {
        #[trusted]
        pub fn new(inner_mut: &'a mut u32) -> Self {
            T { inner: inner_mut, mutex: Mutex::new(()) }
        }

        #[ensures(snap(&self) === old(snap(&self)))]
        #[ensures(result == *self.inner)]
        pub fn query(&mut self) -> u32 {
            *self.inner
        }

        #[trusted]
        pub fn increment(&self) {
            let _guard = self.mutex.lock();
            // SAFETY: We are holding the mutex, so we have unique access to
            // self.inner.
            unsafe {
                let ptr: *mut *mut u32 = std::mem::transmute(&self.inner);
                **ptr = **ptr + 1;
            }
        }
    }
}

fn test_1(mut t: lib::T<'_>) {
    let a = t.query();

    // This call uses interior mutability to change the internal state via a shared reference!
    t.increment();

    let b = t.query();

    // The following assertion fails at runtime, so a verifier must report a verification error.
    assert!(a == b); //~ ERROR the asserted expression might not hold
}

fn test_2(mut t: lib::T<'_>) {
    let a = t.query();

    // Here there might be interference on `t.inner` due to other threads.

    let b = t.query();

    // A conservative verifier might report a verification error for the following assertion.
    assert!(a == b); //~ ERROR the asserted expression might not hold
}

fn main() {
    let mut data = 42;
    let mut t = lib::T::new(&mut data);
    test_1(t);
}
