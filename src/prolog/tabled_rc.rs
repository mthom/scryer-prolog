use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

pub type TabledData<T> = HashSet<Rc<T>>;
    
#[derive(Clone, PartialEq, Eq)]
pub struct TabledRc<T: Hash + Eq> {
    atom: Rc<T>,
    table: Rc<RefCell<TabledData<T>>>
}

impl<T: Hash + Eq> Hash for TabledRc<T> {
    fn hash<H: Hasher>(&self, state: &mut H)
    {
        self.atom.hash(state)        
    }
}

impl<T: Hash + Eq> TabledRc<T> {
    pub fn new(atom: T, table: Rc<RefCell<TabledData<T>>>) -> Self {        
        TabledRc { atom: Rc::new(atom), table }
    }
}

impl<T: Hash + Eq> Drop for TabledRc<T> {
    fn drop(&mut self) {
        if Rc::strong_count(&self.atom) == 2 {
            let mut table = self.table.borrow_mut();
            table.deref_mut().remove(&self.atom);
        }
    }
}

impl<T: Hash + Eq> Deref for TabledRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &*self.atom
    }
}

impl<T: Hash + Eq + fmt::Display> fmt::Display for TabledRc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &*self.atom)
    }
}
