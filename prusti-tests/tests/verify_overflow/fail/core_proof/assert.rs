// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_qi_bound_global=10000 -Psmt_qi_bound_trace=200 -Psmt_qi_bound_trace_kind=10 -Psmt_qi_bound_global_kind=20

use prusti_contracts::*;

fn assert1() {
    
}

fn assert2() {
    assert!(true);
}

fn main() {}
