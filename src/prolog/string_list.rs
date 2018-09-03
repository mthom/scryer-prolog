use std::cell::{Cell, Ref, RefCell};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(PartialOrd, PartialEq, Ord, Eq)]
pub struct StringListWrapper(RefCell<String>);

impl Hash for StringListWrapper {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.borrow().hash(state)
    }
}

// cursor is ignored if the double_quotes flag is set to atom
#[derive(Clone)]
pub struct StringList {
    body: Rc<StringListWrapper>,
    cursor: usize, // use this to generate a chars() iterator on the fly,
                   // and skip over the first cursor chars.
    expandable: Rc<Cell<bool>>
}

impl Hash for StringList {
    #[inline]    
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.borrow().as_str(), self.cursor, self.expandable.get()).hash(state);
    }
}

impl PartialOrd for StringList {
    #[inline]    
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.body.cmp(&other.body))
    }
}

impl Ord for StringList {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if self.expandable.get() && !self.expandable.get() {
            Ordering::Greater
        } else if !self.expandable.get() && self.expandable.get() {
            Ordering::Less
        } else {
            self.borrow()[self.cursor ..].cmp(&other.borrow()[other.cursor ..])
        }
    }
}

impl PartialEq for StringList {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.body, &other.body)
    }
}

impl Eq for StringList {}

impl StringList {
    #[inline]
    pub fn new(s: String, expandable: bool) -> Self {
        let body = Rc::new(StringListWrapper(RefCell::new(s)));

        StringList {
            cursor: 0,
            body,
            expandable: Rc::new(Cell::new(expandable))
        }
    }

    #[inline]
    pub fn is_expandable(&self) -> bool {
        self.expandable.get()
    }

    #[inline]
    pub fn set_expandable(&self) {
        self.expandable.set(true);
    }

    #[inline]
    pub fn set_non_expandable(&self) {
        self.expandable.set(false);
    }

    #[inline]
    pub fn push_char(&mut self, c: char) -> Self {
        if self.expandable.get() {
            self.body.0.borrow_mut().push(c);

            let mut new_string_list = self.clone();
            new_string_list.cursor += c.len_utf8();

            new_string_list
        } else {
            self.clone()
        }
    }

    #[inline]
    pub fn append(&mut self, s: &StringList) {
        self.body.0.borrow_mut().extend(s.borrow()[s.cursor ..].chars());
        self.expandable.set(s.expandable.get());
    }

    #[inline]
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    #[inline]
    pub fn head(&self) -> Option<char> {
        self.borrow()[self.cursor ..].chars().next()
    }

    #[inline]
    pub fn tail(&self) -> Self {
        let mut new_string_list = self.clone();

        if let Some(c) = self.head() {
            new_string_list.cursor += c.len_utf8();
        }

        new_string_list
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.borrow().len() == self.cursor
    }

    #[inline]
    pub fn borrow(&self) -> Ref<String> {
        self.body.0.borrow()
    }
}
