// compile-flags: -Pcheck_overflows=false -Pcheck_panics=false
fn rand<T>() -> T { unimplemented!() }

fn main() {}

fn original_main() {
  let mut x = 0;
  let mut y = 0;
  let p = if rand() { &mut x } else { &mut y };
  *p = 1;
  x += 1;
  assert!(x < 2);
}
