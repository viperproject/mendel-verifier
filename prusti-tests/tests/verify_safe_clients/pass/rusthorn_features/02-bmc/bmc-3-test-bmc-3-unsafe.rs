// compile-flags: -Pcheck_overflows=false -Pcheck_panics=false
fn rand<T>() -> T { unimplemented!() }

fn main(){}

fn original_main() {
  let mut p = 0;
  if rand() {
    p += 1;
  } else {
    p += 2;
  }
  if rand() {
    p += 1;
  } else {
    p += 2;
  }
  if rand() {
    p += 1;
  } else {
    p += 2;
  }
  if rand() {
    p += 1;
  } else {
    p += 2;
  }
  if rand() {
    p += 1;
  } else {
    p += 2;
  }
  if rand() {
    p += 1;
  } else {
    p += 3;
  }
  assert!(p <= 12);
}
