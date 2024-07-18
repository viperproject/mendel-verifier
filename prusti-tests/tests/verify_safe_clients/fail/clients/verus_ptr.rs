#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/lib_verus_ptr.rs"]
mod verus_ptr_lib;
use verus_ptr_lib::*;
/* EVALUATION:IGNOREBEFORE */

#[requires(perm.pptr_id() == ptr.id())]
#[ensures(result.id() == old(ptr.id()))]
#[ensures(result === old(ptr))]
fn read_and_move_ptr<T>(ptr: PPtr<T>, perm: &PointsTo<T>) -> PPtr<T> {
    let _ = ptr.borrow(perm);
    ptr
}

/// Test framing and modifications of the target of the pointer
fn test_1() {
    let (mut initial_ptr, mut perm) = PPtr::new(0);
    assert!(*initial_ptr.borrow(&perm) == 0);

    let mut ptr = read_and_move_ptr(initial_ptr, &perm);

    let data = ptr.verified_borrow_mut(&mut perm);
    assert!(*data == 0);
    *data = 123;
    assert!(*data == 123);
    assert!(*ptr.borrow(&perm) == 123);

    ptr.dispose(perm);


}

/// Test non-aliasing
#[requires(ptr_a.id() == perm_a.pptr_id() && ptr_a.as_ptr() == perm_a.as_ptr())]
#[requires(ptr_b.id() == perm_b.pptr_id() && ptr_b.as_ptr() == perm_b.as_ptr())]
fn test_2(ptr_a: &PPtr<i32>, ptr_b: &PPtr<i32>, perm_a: &PointsTo<i32>, perm_b: &mut PointsTo<i32>) {
    assert!(ptr_a.as_ptr() != ptr_b.as_ptr());
    assert!(ptr_a as *const _ != ptr_b as *const _);

    let initial = *ptr_a.borrow(perm_a);
    *ptr_b.verified_borrow_mut(perm_b) = 123;
    assert!(*ptr_a.borrow(perm_a) == initial);


}

/// Test possible aliasing of pointers to zero-size types
#[requires(ptr_a.id() == perm_a.pptr_id() && ptr_a.as_ptr() == perm_a.as_ptr())]
#[requires(ptr_b.id() == perm_b.pptr_id() && ptr_b.as_ptr() == perm_b.as_ptr())]
fn test_3(ptr_a: &PPtr<()>, ptr_b: &PPtr<()>, perm_a: &mut PointsTo<()>, perm_b: &PointsTo<()>) {
    assert!(ptr_a.as_ptr() != ptr_b.as_ptr()); //~ ERROR
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
