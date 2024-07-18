#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/lib_verus_cell.rs"]
mod verus_cell_lib;
use verus_cell_lib::*;
/* EVALUATION:IGNOREBEFORE */

fn test_1() {
    let (mut cell, mut perm) = PCell::new(0);
    assert!(cell.get(&mut perm) == 0);

    cell.set(&mut perm, 42);
    assert!(cell.get(&mut perm) == 42);

    *cell.get_mut(&mut perm) += 100;
    assert!(cell.get(&perm) == 142);


}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
