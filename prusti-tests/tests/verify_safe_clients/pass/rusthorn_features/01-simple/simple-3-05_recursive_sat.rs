// compile-flags: -Pcheck_overflows=false -Pcheck_panics=false
fn rand<T>() -> T { unimplemented!() }

fn id(x: i32) -> i32 {
  if x == 0 {
    return 0;
  }
  let ret = id2(x - 1) + 1;
  if ret > 2 {
    return 2;
  }
  ret
}

fn id2(x: i32) -> i32 {
  if x == 0 {
    return 0;
  }
  let ret = id(x - 1) + 1;
  if ret > 2 {
    return 2;
  }
  ret
}

fn main(){}

fn original_main() {
  let input = rand();
  let result = id(input);
  assert!(result == 3);
}
