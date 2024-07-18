
pub enum T {
    T1(i32),
    T2(i32),
}

fn main() {
    let mut x = T::T1(111);
    let mut y = &mut x;
    assert!(if let T::T1(z) = y { *z == 111 } else { false });
    assert!(if let T::T1(z) = y { *z == 111 } else { false });

    
}
