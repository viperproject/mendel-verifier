
pub struct A<'a, 'b> {
    pub a1: &'a i32,
    pub a2: B,
    pub a3: C,
    pub a4: &'a D<'b>,
    pub a5: &'a mut D<'b>,
}

pub enum B {
    B(u32),
}

pub enum C {
    C1(usize),
    C2(isize),
}

pub enum D<'a> {
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
    assert!(*a.a1 == 111);
    assert!(if let B::B(y) = a.a2 { y == 222 } else { false });
    assert!(if let C::C1(y) = a.a3 { y == 333 } else { false });
    assert!(if let D::D3(C::C2(y)) = a.a4 { *y == 444 } else { false });
    assert!(if let D::D1(y) = a.a5 { **y == 111 } else { false });

    assert!(false); //~ ERROR the asserted expression might not hold
}
