fn main() {
    let mut a = true;
    let mut b = 1i32;
    let mut c = 2u32;
    let mut d = ();
    let mut e = (1, 2, 3);
    let mut f = (a, b, c, d, e);

    let e_element_0 = e.0;
    let e_element_1 = e.1;
    let e_element_2 = e.2;
    let f_element_0 = f.0;
    let f_element_1 = f.1;
    let f_element_2 = f.2;
    let f_element_3 = f.3;
    let f_element_4 = f.4;

    let mutable_a = &mut a;
    let mutable_b = &mut b;
    let mutable_c = &mut c;
    let mutable_d = &mut d;
    let mutable_e = &mut e;
    let mutable_f = &mut f;

    let tuple_of_mutable_refs = (mutable_a, mutable_b, mutable_c, mutable_d, mutable_e, mutable_f);

    let shared_a = &a;
    let shared_b = &b;
    let shared_c = &c;
    let shared_d = &d;
    let shared_e = &e;
    let shared_f = &f;

    let nested_a = &&&shared_a;
    let nested_b = &&&shared_b;
    let nested_c = &&&shared_c;
    let nested_d = &&&shared_d;
    let nested_e = &&&shared_e;
    let nested_f = &&&shared_f;

    let tuple_of_shared_refs = (nested_a, nested_b, nested_c, nested_d, nested_e, nested_f);

    let a2 = *shared_a;
    let b2 = *shared_b;
    let c2 = *shared_c;
    let d2 = *shared_d;
    let e2 = *shared_e;
    let f2 = *shared_f;
}
