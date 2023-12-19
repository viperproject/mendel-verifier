enum B {
    B(),
}

enum C<'a> {
    C1(),
    C2(&'a i32, u8, u64, i64),
    C3(&'a mut B),
}

struct A<'a, 'b> {
    a1: &'a i32,
    a2: B,
    a3: &'a mut C<'b>,
}

fn main() {
    let x = 111;
    let mut b = B::B();
    let mut c = C::C2(&x, 111, 222, 333);
    let mut a = A {
        a1: &x,
        a2: b,
        a3: &mut c,
    };
    match a.a2 {
        B::B() => {}
    }
    match &&&a.a3 {
        C::C1() => {}
        C::C2(r1, v1, v2, v3) => {}
        C::C3(r1) => {}
    }
}
