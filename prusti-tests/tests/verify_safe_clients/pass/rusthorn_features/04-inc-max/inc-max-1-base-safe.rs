// compile-flags: -Pcheck_overflows=false -Pcheck_panics=false
fn rand<T>() -> T { unimplemented!() }

fn take_max<'a>(ma: &'a mut i32, mb: &'a mut i32) -> &'a mut i32 {
  if *ma >= *mb {
    ma
  } else {
    mb
  }
}
fn main(){}

fn original_main() {
  let mut a = rand();
  let mut b = rand();
  let mc = take_max(&mut a, &mut b);
  *mc += 1;
  assert!(a != b);
}
