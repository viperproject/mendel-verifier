#[analyzer::run]
fn mut_ref_arg(x: &mut u32) {
    *x -= 1;
    *x += 1;
}

#[analyzer::run]
fn mut_ref_in_arg(x: (u32, (&mut u32, u32))) {
    *x.1.0 -= 1;
    *x.1.0 += 1;
}

fn main() {}
