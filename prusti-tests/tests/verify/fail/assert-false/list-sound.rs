#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;

enum List {
    Nil,
    Const {
        val: i32,
        next: Box<List>
    },
}

fn head(list: List) -> Option<i32> {
    let ret = match list {
        List::Nil => None,
        List::Const { val, box next } => Some(val),
    };
    
    ret
}

fn tail(list: List) -> Option<List> {
    let ret = match list {
        List::Nil => None,
        List::Const { val, box next } => Some(next),
    };
    
    ret
}

fn length(list: List) -> u32 {
    let ret = match list {
        List::Nil => 0,
        List::Const { val, box next } => 1 + length(next),
    };
    
    ret
}

fn last_value(list: List) -> Option<i32> {
    let ret = match list {
        List::Nil => None,
        List::Const { val, box next } => match last_value(next) {
            None => Some(val),
            Some(last) => Some(last),
        }
    };
    
    ret
}

fn empty_list(val: i32) -> List {
    
    List::Nil
}

fn singleton_list(val: i32) -> List {
    let ret = List::Const {
        val,
        next: box List::Nil
    };
    
    ret
}

fn prepend(val: i32, list: List) -> List {
    let ret = List::Const {
        val,
        next: box list
    };
    
    ret
}

fn append(new_val: i32, list: List) -> List {
    let ret = match list {
        List::Nil => List::Const {
            val: new_val,
            next: box List::Nil
        },
        List::Const { val, box next } => List::Const {
            val: val,
            next: box append(new_val, next)
        },
    };
    
    ret
}

fn revert(list: List) -> List {
    let ret = match list {
        List::Nil => List::Nil,
        List::Const { val, box next } => append(val, revert(next))
    };
    
    ret
}

fn main() {}
