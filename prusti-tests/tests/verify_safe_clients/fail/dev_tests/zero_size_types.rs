#![allow(dead_code)]
use prusti_contracts::*;

#[repr(transparent)]
struct ZST {
    first: (),
    second: (),
}

#[trusted]
#[ensures(result.0 as *const _ == result.1 as *const _)]
fn unpack_mut(x: &mut ZST) -> (&mut (), &mut ()) {
    (&mut x.first, &mut x.second)
}

fn main() {
    let mut x = ZST { first: (), second: () };
    let (y, z) = unpack_mut(&mut x);
    assert!(y as *const _ == z as *const _);
    assert!(y as *const _ != z as *const _); //~ ERROR
}
