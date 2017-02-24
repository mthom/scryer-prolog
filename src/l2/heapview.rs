use l2::ast::*;

use std::vec::Vec;

#[derive(Clone, Copy)]
pub enum HeapCellView<'a> {
    Str(usize, &'a Atom),
    Var(usize)
}

pub struct HeapCellViewer<'a> {
    heap: &'a Heap,
    state_stack: Vec<(usize, &'a HeapCellValue)>
}

impl<'a> HeapCellViewer<'a> {
    pub fn new(heap: &'a Heap, focus: usize) -> Self {
        HeapCellViewer {
            heap: heap,
            state_stack: vec![(focus, &heap[focus])]
        }
    }

    fn follow(&self, value: &'a HeapCellValue) -> &'a HeapCellValue {
        match value {
            &HeapCellValue::NamedStr(_, _) => value,
            &HeapCellValue::Ref(cell_num) | &HeapCellValue::Str(cell_num) =>
                &self.heap[cell_num],
        }
    }
}

impl<'a> Iterator for HeapCellViewer<'a> {
    type Item = HeapCellView<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(hcv) = self.state_stack.pop() {
            match hcv {
                (focus, &HeapCellValue::NamedStr(arity, ref name)) => {
                    for i in (1 .. arity + 1).rev() {
                        self.state_stack.push((focus + i, &self.heap[focus + i]));
                    }                            
                    
                    return Some(HeapCellView::Str(arity, name));
                },
                (_, &HeapCellValue::Ref(cell_num)) => {
                    let new_hcv = self.follow(hcv.1);

                    if hcv.1 == new_hcv {
                        return Some(HeapCellView::Var(cell_num));
                    } else {
                        self.state_stack.push((cell_num, new_hcv));
                    }
                },
                (_, &HeapCellValue::Str(cell_num)) => {
                    let new_hcv = self.follow(hcv.1);
                    self.state_stack.push((cell_num, new_hcv));
                }
            }
        }

        None
    }
}
