use std::cell::{RefCell, RefMut};
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::{Rc};

pub struct TabledData<T> {
    table: Rc<RefCell<HashSet<Rc<T>>>>,
    pub(crate) module_name: Rc<String>
}

impl<T: Hash + Eq + fmt::Debug> fmt::Debug for TabledData<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TabledData")
            .field("table", &self.table)
            .field("module_name", &self.table)
            .finish()
    }
}

impl<T> Clone for TabledData<T> {
    fn clone(&self) -> Self {
        TabledData { table: self.table.clone(),
                     module_name: self.module_name.clone() }
    }
}

impl<T: PartialEq> PartialEq for TabledData<T> {
    fn eq(&self, other: &TabledData<T>) -> bool
    {
        Rc::ptr_eq(&self.table, &other.table) && self.module_name == other.module_name
    }
}

impl<T: Hash + Eq> TabledData<T> {
    #[inline]
    pub fn new(module_name: Rc<String>) -> Self {
        TabledData {
            table: Rc::new(RefCell::new(HashSet::new())),
            module_name
        }
    }

    #[inline]
    pub fn borrow_mut(&self) -> RefMut<HashSet<Rc<T>>> {
        self.table.borrow_mut()
    }
}

pub struct TabledRc<T: Hash + Eq> {
    pub(crate) atom: Rc<T>,
    pub table: TabledData<T>
}

impl<T: Hash + Eq + fmt::Debug> fmt::Debug for TabledRc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TabledRc")
            .field("atom", &self.atom)
            .field("table", &self.table)
            .finish()
    }
}

// this Clone instance is manually defined to prevent the compiler
// from complaining when deriving Clone for StringList.
impl<T: Hash + Eq> Clone for TabledRc<T> {
    fn clone(&self) -> Self {
        TabledRc { atom: self.atom.clone(), table: self.table.clone() }
    }
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

impl<T: Hash + Eq + ToString> TabledRc<T> {
    pub fn new(atom: T, table: TabledData<T>) -> Self {
        let atom = match table.borrow_mut().take(&atom) {
            Some(atom) => atom.clone(),
            None => Rc::new(atom)
        };

        table.borrow_mut().insert(atom.clone());

        TabledRc { atom, table }
    }

    #[inline]
    pub fn inner(&self) -> Rc<T> {
        self.atom.clone()
    }

    #[inline]
    pub(crate) fn owning_module(&self) -> Rc<String> {
        self.table.module_name.clone()
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

#[macro_export]
macro_rules! tabled_rc {
    ($e:expr, $tbl:expr) => (
        TabledRc::new(String::from($e), $tbl.clone())
    )
}
