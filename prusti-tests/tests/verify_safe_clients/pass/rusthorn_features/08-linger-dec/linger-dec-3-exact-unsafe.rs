// compile-flags: -Pcheck_overflows=false -Pcheck_panics=false
fn rand<T>() -> T { unimplemented!() }

fn linger_dec_bound(n: i32, ma: &mut i32) {
  if n == 0 {
    return;
  }
  *ma -= 1;
  let mut b = rand();
  linger_dec_bound(n - 1, if rand() { &mut b } else { ma });
}
fn main(){}

fn original_main() {
  let n = rand();
  let mut a = rand();
  let a0 = a;
  linger_dec_bound(n, &mut a);
  assert!(a0 >= a && a0 - a < n);
}
