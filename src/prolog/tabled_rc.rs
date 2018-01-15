use std::cell::RefCell;
use std::collections::HashSet;
use std::hash::Hash;
use std::ops::Deref;
use std::rc::Rc;

pub type TabledData<T> = HashSet<Rc<T>>;
    
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TabledRc<T: Hash + Eq> {
    atom: Rc<T>,
    table: Rc<RefCell<TabledData<T>>>
}

impl<T: Hash + Eq> TabledRc<T> {
    pub fn new(atom: T, table: Rc<RefCell<TabledData<T>>>) -> Self {
        TabledRc { atom: Rc::new(atom), table }
    }
}

impl<T: Hash + Eq> Drop for TabledRc<T> {
    fn drop(&mut self) {
        if Rc::strong_count(&self.atom) == 2 {
            let table = *self.table.borrow_mut();
            table.remove(&self.atom);
        }
    }
}

impl<T: Hash + Eq> Deref for TabledRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &*self.atom
    }
}
