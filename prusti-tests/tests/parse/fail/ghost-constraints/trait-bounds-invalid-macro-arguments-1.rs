use prusti_contracts::*;

#[ghost_constraint([ //~ ERROR: expected `,`
    ensures(result > 0)
])]
//~| ERROR: expected a trait bound `T: A + B` and specifications in brackets `[requires(...), ensures(...), pure, ...]`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
