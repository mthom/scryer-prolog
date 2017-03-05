use l3::and_stack::*;
use l3::ast::*;

use std::vec::Vec;

#[derive(Clone, Copy)]
pub enum HeapCellView<'a> {
    Str(usize, &'a Atom),
    HeapVar(usize),
    StackVar(usize, usize)
}

pub struct HeapCellViewer<'a> {
    heap: &'a Heap,
    and_stack: &'a AndStack,
    state_stack: Vec<Addr>
}

impl<'a> HeapCellViewer<'a> {
    pub fn new(heap: &'a Heap, and_stack: &'a AndStack, focus: Addr) -> Self {
        HeapCellViewer {
            heap: heap,
            and_stack: and_stack,
            state_stack: vec![focus]
        }
    }

    fn follow_stack_ref(&mut self, mut fr: usize, mut sc: usize) -> HeapCellView<'a>
    {
        loop {
            match self.and_stack[fr][sc] {
                Addr::HeapCell(hc) | Addr::Str(hc) =>
                    return self.follow_heap_ref(hc),
                Addr::StackCell(fr1, sc1) => {
                    if fr1 == fr && sc1 == sc {
                        return HeapCellView::StackVar(fr, sc);
                    }

                    fr = fr1; sc = sc1;
                }
            }
        }
    }

    fn follow_heap_ref(&mut self, mut focus: usize) -> HeapCellView<'a> {
        loop {
            match &self.heap[focus] {
                &HeapCellValue::NamedStr(arity, ref name) => {
                    for i in (1 .. arity + 1).rev() {
                        self.state_stack.push(Addr::HeapCell(focus + i));
                    }

                    return HeapCellView::Str(arity, name);
                },
                &HeapCellValue::Ref(Ref::HeapCell(hc)) => {
                    if focus == hc {
                        return HeapCellView::HeapVar(hc);
                    } else {
                        focus = hc;
                    }
                },
                &HeapCellValue::Ref(Ref::StackCell(fr, sc)) =>
                    return self.follow_stack_ref(fr, sc),
                &HeapCellValue::Str(cell_num) =>
                    focus = cell_num,
            }
        }
    }
}

impl<'a> Iterator for HeapCellViewer<'a> {
    type Item = HeapCellView<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(addr) = self.state_stack.pop() {
            match addr {
                Addr::HeapCell(hc) | Addr::Str(hc) =>
                    return Some(self.follow_heap_ref(hc)),
                Addr::StackCell(fr, sc) =>
                    return Some(self.follow_stack_ref(fr, sc))
            }
        }

        None
    }
}
