use prolog::ast::*;

use std::cell::RefCell;
use std::rc::Rc;

pub type TabledData<T> = HashSet<Rc<T>>
    
pub struct TabledRc<T> {
    atom: Rc<T>,
    table: Rc<RefCell<TabledData<T>>>
}
