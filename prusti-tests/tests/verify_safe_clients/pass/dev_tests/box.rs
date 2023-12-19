fn test(
    y: Box<u32>,
    z: Box<Box<u32>>,
) {}

fn main() {
    let x: u32 = 123;
    let y = Box::new(x);
    let z = Box::new(y);
}
