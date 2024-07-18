use prusti_contracts::*;

fn borrow(_x: &u32) {}

pub fn test1(a: u32, b: u32, cond: bool) {
    let x;
    if cond {
        x = &a;
    } else {
        x = &b;
    }
    borrow(x);
    
}

pub fn test1_1(a: u32, b: u32, cond: bool) {
    let x;
    if cond {
        x = &a;
        
    } else {
        x = &b;
    }
    borrow(x);
}

pub fn test1_2(a: u32, b: u32, cond: bool) {
    let x;
    if cond {
        x = &a;
    } else {
        x = &b;
        
    }
    borrow(x);
}

pub fn test2(a: u32, b: u32, cond: bool) {
    let x;
    if cond {
        x = &a;
    } else {
        x = &b;
    }
    let _y = x;
    
}

pub fn test3(cond: bool) {
    let mut a = 5;
    let mut b = 6;
    let x;
    if cond {
        x = &a;
    } else {
        x = &b;
    }
    borrow(x);
    if cond {
        assert!(*x == 5);
    } else {
        assert!(*x == 6);
    }
    a = 7;
    b = 8;
    assert!(a == 7 && b == 8);
    
}

pub fn test3_1(cond: bool) {
    let mut a = 5;
    let mut b = 6;
    let x;
    if cond {
        x = &a;
    } else {
        x = &b;
    }
    borrow(x);
    if cond {
        assert!(*x == 5);
        
    } else {
        assert!(*x == 6);
    }
    a = 7;
    b = 8;
    assert!(a == 7 && b == 8);
}

pub fn test3_2(cond: bool) {
    let mut a = 5;
    let mut b = 6;
    let x;
    if cond {
        x = &a;
    } else {
        x = &b;
    }
    borrow(x);
    if cond {
        assert!(*x == 5);
    } else {
        assert!(*x == 6);
        
    }
    a = 7;
    b = 8;
    assert!(a == 7 && b == 8);
}

fn main() {
}
