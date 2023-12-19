struct A<'a, 'b> {
    a1: &'a i32,
    a2: B,
    a3: C,
    a4: &'a D<'b>,
    a5: &'a mut D<'b>,
}

enum B {
    B(u32),
}

enum C {
    C1(usize),
    C2(isize),
}

enum D<'a> {
    D1(&'a i32),
    D2(i8, u8, u64, i64),
    D3(&'a mut C),
}

fn main() {
    let x = 111;
    let mut b = B::B(222);
    let mut c1 = C::C1(333);
    let mut c2 = C::C2(444);
    let mut d1 = D::D3(&mut c2);
    let mut d2 = D::D1(&x);
    let mut a = A {
        a1: &x,
        a2: b,
        a3: c1,
        a4: &d1,
        a5: &mut d2,
    };
}