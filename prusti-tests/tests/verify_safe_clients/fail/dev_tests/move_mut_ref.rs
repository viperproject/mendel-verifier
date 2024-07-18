use prusti_contracts::*;

/// Converts a raw pointer to the referenced instance.
/// - `ghost`: This is only allowed in specifications, or it would be unsound.
/// - `pure_unstable`: The result of this function might change even between consecutive calls.
/// - `unsafe { .. }`: This trick should only allowed in ghost code, or it would be unsound.
#[ghost_fn]
#[trusted]
#[pure_unstable]
#[ensures(unsafe { snap(&*ptr) } ==== result)]
pub fn deref<T>(ptr: *const T) -> T {
    unimplemented!()
}

struct BadBox<T>(*mut T);

#[capable(&mut self => writeRef(self.as_ptr()))]
impl<T> BadBox<T> {}

impl<T> BadBox<T> {
    #[trusted]
    #[ensures(deref(result.as_ptr()) ==== old(x))]
    fn new(x: T) -> Self {
        let ptr = Box::into_raw(Box::new(x));
        BadBox(ptr)
    }

    #[pure]
    fn as_ptr(&self) -> *const T {
        self.0
    }

    #[trusted]
    #[ensures(result as *const _ == old(self.as_ptr()))]
    #[ensures(*result ==== old(deref(self.as_ptr())))]
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.0 }
    }
}

fn move_mut_ref_primitive() {
    let mut x = 123;
    let y = &mut x;
    assert!(*y == 123);
    let z = y;
    assert!(*z == 123);
    assert!(x == 123);


}

fn move_mut_ref_badbox() {
    let mut x = BadBox::new(123);
    let y = x.as_mut();
    let ptr = y as *mut _;
    prusti_assert!(deref(ptr) == 123); // Succeeds
    let v = *y;
    prusti_assert!(ptr as *const _ == x.as_ptr()); // Succeeds

    prusti_assert!(deref(ptr) == 123);
    assert!(*x.as_mut() == 123);


}

fn test_ref_mut(x: &mut i32) {
    *x = 123;
    assert!(*x == 123);

    *x = 42;
    assert!(*x == 42);


}

fn main() {}
