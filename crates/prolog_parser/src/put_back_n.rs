use std::iter::Peekable;

#[derive(Debug, Clone)]
pub struct PutBackN<I: Iterator> {
    top: Vec<I::Item>,
    iter: Peekable<I>,
}

pub fn put_back_n<I>(iterable: I) -> PutBackN<I::IntoIter>
    where I: IntoIterator
{
    PutBackN {
        top: Vec::new(),
        iter: iterable.into_iter().peekable(),
    }
}

impl<I: Iterator> PutBackN<I> {
    #[inline]
    pub(crate)
    fn put_back(&mut self, item: I::Item) {
        self.top.push(item);
    }

    #[inline]
    pub fn take_buf(&mut self) -> Vec<I::Item> {
        std::mem::replace(&mut self.top, vec![])
    }

    #[inline]
    pub(crate)
    fn peek(&mut self) -> Option<&I::Item> {
        if self.top.is_empty() {
            /* This is a kludge for Ctrl-D not being
             * handled properly if self.iter().peek() isn't called
             * first. */
            match self.iter.peek() {
                Some(_) => {
                    self.iter.next().and_then(move |item| {
                        self.top.push(item);
                        self.top.last()
                    })
                }
                None => {
                    None
                }
            }
        } else {
            self.top.last()
        }
    }

    #[inline]
    pub(crate)
    fn put_back_all<DEI: DoubleEndedIterator<Item = I::Item>>(&mut self, iter: DEI) {
        self.top.extend(iter.rev());
    }
}

impl<I: Iterator> Iterator for PutBackN<I> {
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        if self.top.is_empty() {
            self.iter.next()
        } else {
            self.top.pop()
        }
    }
}
