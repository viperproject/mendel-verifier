
fn example(mut pair: (u32, u32), cond: bool) {
    let element: &mut u32;

    if cond {
        pair.0 = 1;
        pair.1 = 2;
        element = &mut pair.0;
    } else {
        pair.0 = 3;
        pair.1 = 4;
        element = &mut pair.1;
    }

    let dummy = 0;
    assert!(dummy == 0);

    assert!(*element >= 1);

    if cond {
        assert!(pair.0 == 1);

        assert!(pair.1 == 2); // Incompleteness, due to conditionally unreachable places.
        //~^ ERROR the asserted expression might not hold
    } else {
        assert!(pair.0 == 3); // Incompleteness, due to conditionally unreachable places.
        //~^ ERROR the asserted expression might not hold

        assert!(pair.1 == 4);
    }

    assert!(false) //~ ERROR the asserted expression might not hold
}

fn main() {}
