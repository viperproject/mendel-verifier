#[analyzer::run]
fn move_unit_shared_ref() {
    let unit = ();
    let unit_ref = &unit;
    let tuple = (unit_ref, unit_ref);
}

#[analyzer::run]
fn move_unit_mutable_ref() {
    let mut unit1 = ();
    let mut unit2 = ();
    let unit_ref1 = &mut unit1;
    let unit_ref2 = &mut unit2;
    let tuple = (unit_ref1, unit_ref2);
}

fn main() {}
