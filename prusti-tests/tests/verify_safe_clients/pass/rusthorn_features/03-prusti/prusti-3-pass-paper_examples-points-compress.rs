// compile-flags: -Pcheck_overflows=false -Pcheck_panics=false
fn rand<T>() -> T { unimplemented!() }

struct Point {
  x: i32,
  y: i32,
}

fn shift_x(p: &mut Point, s: i32) { p.x = p.x + s }

fn main(){}

fn original_main() {
  let mut segm: (Box<Point>, Box<Point>) = rand();
  let diff = (*segm.0).x - (*segm.1).x + 1;
  shift_x(&mut segm.1, diff);
  assert!((*segm.0).x < (*segm.1).x);
}
