
struct T {
    a: String,
    b: String,
    c: String,
}

struct U {
    t: T,
    d: String,
}

#[analyzer::run]
fn main() {
    let mut t = T { a: "a".to_string(), b: "b".to_string(), c: "c".to_string() };
    let mut u = U { t, d: "d".to_string() };
    let mut x = &mut u;
    let mut y = &mut (*(&mut (*x).t)).b;
    drop(y);
    drop(x);
}
