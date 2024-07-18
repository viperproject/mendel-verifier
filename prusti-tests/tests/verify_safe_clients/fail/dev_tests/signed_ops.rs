use prusti_contracts::*;

// To inhibit constant-propagation optimizations:
#[pure]
fn id<T: Copy>(x: T) -> T { x }

fn check_division(){
    assert!(id(3i32) / 2 == 1);
    assert!(id(-3i32) / 2 == -1);
    assert!(id(3i32) / -2 == -1);
    assert!(id(-3i32) / -2 == 1);
    prusti_assert!(id(3i32) / 2 == 1);
    prusti_assert!(id(-3i32) / 2 == -1);
    prusti_assert!(id(3i32) / -2 == -1);
    prusti_assert!(id(-3i32) / -2 == 1);


}

fn check_modulo() {
    assert!(id(10) % 3 == 1);
    assert!(id(10) % -3 == 1);
    assert!(id(-10) % 3 == -1);
    assert!(id(-10) % -3 == -1);
    prusti_assert!(id(10) % 3 == 1);
    prusti_assert!(id(10) % -3 == 1);
    prusti_assert!(id(-10) % 3 == -1);
    prusti_assert!(id(-10) % -3 == -1);


}

fn main(){}
