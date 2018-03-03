use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

pub type TabledData<T> = Rc<RefCell<HashSet<Rc<T>>>>;

#[derive(Clone)]
pub struct TabledRc<T: Hash + Eq> {
    atom: Rc<T>,
    table: TabledData<T>
}

impl<T: Ord + Hash + Eq> PartialOrd for TabledRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>
    {
        Some(self.atom.cmp(&other.atom))
    }
}

impl<T: Ord + Hash + Eq> Ord for TabledRc<T> {
    fn cmp(&self, other: &Self) -> Ordering
    {
        self.atom.cmp(&other.atom)
    }
}

impl<T: Hash + Eq> PartialEq for TabledRc<T> {
    fn eq(&self, other: &TabledRc<T>) -> bool
    {
        self.atom == other.atom
    }
}

impl<T: Hash + Eq> Eq for TabledRc<T> {}

impl<T: Hash + Eq> Hash for TabledRc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.atom.hash(state)
    }
}

impl<T: Hash + Eq> TabledRc<T> {
    pub fn new(atom: T, table: TabledData<T>) -> Self {
        let atom = match table.borrow_mut().take(&atom) {
            Some(atom) => atom.clone(),
            None => Rc::new(atom)
        };

        table.borrow_mut().insert(atom.clone());

        TabledRc { atom, table }
    }

    pub fn atom_tbl(&self) -> TabledData<T> {
        self.table.clone()
    }
}

impl<T: Hash + Eq> Drop for TabledRc<T> {
    fn drop(&mut self) {
        if Rc::strong_count(&self.atom) == 2 {
            self.table.borrow_mut().remove(&self.atom);
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
