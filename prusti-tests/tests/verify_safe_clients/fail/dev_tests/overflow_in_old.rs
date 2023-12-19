use prusti_contracts::*;

pub struct List {
    pub sz: usize
}

impl List {
    #[ensures(result.sz == 0)]
    fn new() -> List {
        List {
            sz: 0,
        }
    }

    #[requires(self.sz == 0)]
    #[ensures(self.sz == 1)]
    #[ensures(old(0 - self.sz) == 0)] //~ ERROR old expression contains a checked operation
    fn add_to_empty(&mut self) {
        self.sz += 1;
    }
}

fn main() {
    let mut l = List::new();

    l.add_to_empty(); //~ ERROR old expression contains a checked operation

    assert!(false);
}
