use prolog::and_stack::*;
use prolog::ast::*;

use std::vec::Vec;

#[derive(Clone, Copy)]
pub enum TToken {
    Bar,
    Comma,
    LRBracket,
    LSBracket(usize),
    Nothing,
    RRBracket,
    RSBracket
}

impl TToken {
    pub fn as_str(self) -> &'static str {
        match self {
            TToken::Bar => " | ",
            TToken::Comma => ", ",
            TToken::LRBracket => "(",
            TToken::LSBracket(_) => "[",
            TToken::Nothing   => "",
            TToken::RRBracket => ")",
            TToken::RSBracket => "]"
        }
    }
}

#[derive(Clone, Copy)]
enum CellRef<'a> {
    View(CellView<'a>),
    Redirect(usize),
    TToken(TToken)
}

#[derive(Clone, Copy)]
pub enum CellView<'a> {
    Con(&'a Constant),
    HeapVar(usize),
    StackVar(usize, usize),
    Str(usize, &'a Atom),
    TToken(TToken),
}

pub struct HeapCellViewer<'a> {
    and_stack: &'a AndStack,
    heap: &'a Heap,
    state_stack: Vec<CellRef<'a>>
}

impl<'a> HeapCellViewer<'a> {
    fn cell_ref_from_addr(&self, mut focus: &'a Addr) -> CellRef<'a> {
        loop {
            match focus {
                &Addr::Con(ref c) =>
                    return CellRef::View(CellView::Con(c)),
                &Addr::Lis(hc) | &Addr::HeapCell(hc) | &Addr::Str(hc) =>
                    return CellRef::Redirect(hc),
                &Addr::StackCell(fr, sc) => {
                    match &self.and_stack[fr][sc] {
                        &Addr::StackCell(fr1, sc1) => {
                            if fr1 == fr && sc1 == sc {
                                return CellRef::View(CellView::StackVar(fr, sc));
                            }
                        },
                        _ => focus = &self.and_stack[fr][sc]
                    }
                }
            }
        }
    }

    pub fn new(heap: &'a Heap, and_stack: &'a AndStack, addr: &'a Addr) -> Self
    {
        let mut viewer = HeapCellViewer {
            heap: heap,
            and_stack: and_stack,
            state_stack: vec![]
        };

        let cell_ref = viewer.cell_ref_from_addr(addr);
        let view = viewer.follow(cell_ref);

        viewer.state_stack.push(CellRef::View(view));

        viewer
    }

    pub fn remove_token(&mut self, loc: usize) {
        self.state_stack[loc] = CellRef::TToken(TToken::Nothing);
    }

    pub fn peek(&mut self) -> Option<CellView<'a>> {
        let len = self.state_stack.len();

        if len > 0 {
            let last_elt  = self.state_stack.pop().unwrap();
            let cell_view = self.follow(last_elt);

            self.state_stack.truncate(len - 1);
            self.state_stack.push(last_elt);

            Some(cell_view)
        } else {
            None
        }
    }

    fn from_heap(&mut self, mut focus: usize) -> CellView<'a> {
        loop {
            match &self.heap[focus] {
                &HeapCellValue::Con(ref c) =>
                    return CellView::Con(c),
                &HeapCellValue::Lis(a) => {
                    self.state_stack.push(CellRef::TToken(TToken::RSBracket));

                    self.state_stack.push(CellRef::Redirect(a + 1));
                    self.state_stack.push(CellRef::TToken(TToken::Bar));
                    self.state_stack.push(CellRef::Redirect(a));

                    let len = self.state_stack.len() - 4;

                    return CellView::TToken(TToken::LSBracket(len));
                },
                &HeapCellValue::NamedStr(arity, ref name) => {
                    self.state_stack.push(CellRef::TToken(TToken::RRBracket));

                    for i in (2 .. arity + 1).rev() {
                        self.state_stack.push(CellRef::Redirect(focus + i));
                        self.state_stack.push(CellRef::TToken(TToken::Comma));
                    }

                    self.state_stack.push(CellRef::Redirect(focus + 1));
                    self.state_stack.push(CellRef::TToken(TToken::LRBracket));

                    return CellView::Str(arity, name);
                },
                &HeapCellValue::Ref(Ref::HeapCell(hc)) => {
                    if focus == hc {
                        return CellView::HeapVar(hc);
                    } else {
                        focus = hc;
                    }
                },
                &HeapCellValue::Ref(Ref::StackCell(fr, sc)) => {
                    match self.cell_ref_from_addr(&self.and_stack[fr][sc]) {
                        CellRef::View(cell_view) => return cell_view,
                        CellRef::Redirect(hc)    => focus = hc,
                        CellRef::TToken(token)   => return CellView::TToken(token)
                    };
                },
                &HeapCellValue::Str(cell_num) =>
                    focus = cell_num,
            }
        }
    }

    fn follow(&mut self, cell_ref: CellRef<'a>) -> CellView<'a>
    {
        match cell_ref {
            CellRef::Redirect(hc) =>
                self.from_heap(hc),
            CellRef::View(cell_view) =>
                cell_view,
            CellRef::TToken(term_token) =>
                CellView::TToken(term_token)
        }
    }
}


impl<'a> Iterator for HeapCellViewer<'a> {
    type Item = CellView<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cell_ref) = self.state_stack.pop() {
            Some(self.follow(cell_ref))
        } else {
            None
        }
    }
}
