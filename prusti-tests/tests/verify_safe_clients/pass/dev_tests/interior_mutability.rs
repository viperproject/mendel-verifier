use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::{Mutex, RwLock, Arc};

fn test(
    cell: Cell<u32>,
    ref_cell: RefCell<u32>,
    rc: Rc<u32>,
    mutex: Mutex<u32>,
    rw_lock: RwLock<u32>,
    arc: Arc<u32>,
) {}

fn main() {
    let cell = Cell::new(1);
    let ref_cell = RefCell::new(2);
    let rc = Rc::new(3);
    let mutex = Mutex::new(3);
    let rw_lock = RwLock::new(3);
    let arc = Arc::new(3);
}
