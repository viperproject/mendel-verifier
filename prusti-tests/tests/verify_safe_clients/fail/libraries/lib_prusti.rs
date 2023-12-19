// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
/* EVALUATION:IGNOREBEFORE */

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

/// Converts a raw pointer to a shared reference pointing to the same address.
/// - `ghost`: This is only allowed in specifications, or it would be unsound.
/// - `pure_unstable`: The result of this function might change even between consecutive calls.
/// - `unsafe { .. }`: This trick should only allowed in ghost code, or it would be unsound.
#[ghost_fn]
#[trusted]
#[pure_unstable]
#[ensures(ptr ==== result as *const T)]
#[ensures(unsafe { snap(&*ptr) } ==== snap(result))]
pub fn as_ref<'a, T: 'a>(ptr: *const T) -> &'a T {
    unimplemented!()
}
