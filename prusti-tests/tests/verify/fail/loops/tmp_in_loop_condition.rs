#![feature(box_syntax)]

use prusti_contracts::*;

#[trusted]
fn random() -> u32 {
    unimplemented!()
}

fn test1() {
    let mut tmp = box box random();
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;

    while {
        let guard = random() < 55;

        let mut tmp = box box random();
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;

        guard
    } {
        let mut tmp = box box random();
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;
    }

    let mut tmp = box box random();
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;
    
}

fn test2() {
    let mut tmp = box box random();
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;

    while {
        let guard = random() < 55;

        let mut tmp = box box random();
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;

        guard
    } {
        let mut tmp = box box random();
        let tmp_ref = &tmp;
        let tmp_ref_mut = &mut tmp;
        
    }

    let mut tmp = box box random();
    let tmp_ref = &tmp;
    let tmp_ref_mut = &mut tmp;
}

fn main() {}
