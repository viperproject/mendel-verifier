
pub struct T {
    pub a: i32,
    pub b: i32,
    pub c: i32,
}

pub struct U {
    pub t: T,
    pub d: i32,
}

fn main() {
    let mut t = T { a: 1, b: 2, c: 3 };
    let mut u = U { t, d: 4 };
    let mut x = &mut u;
    let mut y = &mut (*(&mut (*x).t)).b;
    assert!(*y == 2);
    assert!(u.t.a == 1);
    assert!(u.t.b == 2);
    assert!(u.t.c == 3);
    assert!(u.d == 4);
    
}
