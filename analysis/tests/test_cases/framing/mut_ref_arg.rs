#[analyzer::run]
fn minus_plus_one(x: &mut u32) {
    *x -= 1;
    *x += 1;
}

fn main() {}
