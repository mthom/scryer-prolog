use crate::prolog::machine::*;

use std::vec::IntoIter;

pub static VERIFY_ATTRS: &str = include_str!("attributed_variables.pl");
pub static PROJECT_ATTRS: &str = include_str!("project_attributes.pl");

pub(super) type Bindings = Vec<(usize, Addr)>;

pub(super) struct AttrVarInitializer {
    pub(super) attribute_goals: Vec<Addr>,
    pub(super) attr_var_queue: Vec<usize>,
    pub(super) bindings: Bindings,
    pub(super) cp: LocalCodePtr,
    pub(super) instigating_p: LocalCodePtr,
    pub(super) verify_attrs_loc: usize,
    pub(super) project_attrs_loc: usize,
}

impl AttrVarInitializer {
    pub(super) fn new(verify_attrs_loc: usize, project_attrs_loc: usize) -> Self {
        AttrVarInitializer {
            attribute_goals: vec![],
            attr_var_queue: vec![],
            bindings: vec![],
            instigating_p: LocalCodePtr::default(),
            cp: LocalCodePtr::default(),
            verify_attrs_loc,
            project_attrs_loc,
        }
    }

    #[inline]
    pub(super) fn reset(&mut self) {
	self.attribute_goals.clear();
        self.attr_var_queue.clear();
        self.bindings.clear();
    }

    #[inline]
    pub(super) fn backtrack(&mut self, queue_b: usize, bindings_b: usize) {
        self.attr_var_queue.truncate(queue_b);
        self.bindings.truncate(bindings_b);
    }
}

impl MachineState {
    pub(super) fn push_attr_var_binding(&mut self, h: usize, addr: Addr) {
        if self.attr_var_init.bindings.is_empty() {
            self.attr_var_init.instigating_p = self.p.local();

            if self.last_call {
                self.attr_var_init.cp = self.cp;
            } else {
                self.attr_var_init.cp = self.p.local() + 1;
            }

            self.p = CodePtr::VerifyAttrInterrupt(self.attr_var_init.verify_attrs_loc);
        }

        self.attr_var_init.bindings.push((h, addr));
    }

    fn populate_var_and_value_lists(&mut self) -> (Addr, Addr) {
        let iter = self
            .attr_var_init
            .bindings
            .iter()
            .map(|(ref h, _)| Addr::AttrVar(*h));

        let var_list_addr = Addr::HeapCell(self.heap.to_list(iter));

        let iter = self
            .attr_var_init
            .bindings
            .drain(0 ..)
            .map(|(_, addr)| addr);

        let value_list_addr = Addr::HeapCell(self.heap.to_list(iter));
        (var_list_addr, value_list_addr)
    }

    fn verify_attributes(&mut self) {
        for (h, _) in &self.attr_var_init.bindings {
            self.heap[*h] = HeapCellValue::Addr(Addr::AttrVar(*h));
        }

        let (var_list_addr, value_list_addr) = self.populate_var_and_value_lists();

        self[temp_v!(1)] = var_list_addr;
        self[temp_v!(2)] = value_list_addr;
    }

    pub(super) fn gather_attr_vars_created_since(&self, b: usize) -> IntoIter<Addr> {
        let mut attr_vars: Vec<_> = self.attr_var_init.attr_var_queue[b..]
            .iter()
            .filter_map(|h| match self.store(self.deref(Addr::HeapCell(*h))) {
                Addr::AttrVar(h) => Some(Addr::AttrVar(h)),
                _ => None,
            })
            .collect();

        attr_vars.sort_unstable_by(|a1, a2| self.compare_term_test(a1, a2));

        self.term_dedup(&mut attr_vars);
        attr_vars.into_iter()
    }

    pub(super) fn verify_attr_interrupt(&mut self, p: usize) {
        self.allocate(self.num_of_args + 2);

        let e = self.e;
        self.stack.index_and_frame_mut(e).prelude.interrupt_cp = self.attr_var_init.cp;

        for i in 1 .. self.num_of_args + 1 {
            self.stack.index_and_frame_mut(e)[i] = self[RegType::Temp(i)].clone();
        }

        self.stack.index_and_frame_mut(e)[self.num_of_args + 1] =
            Addr::Con(Constant::CutPoint(self.b0));
        self.stack.index_and_frame_mut(e)[self.num_of_args + 2] =
            Addr::Con(Constant::Usize(self.num_of_args));

        self.verify_attributes();

        self.num_of_args = 2;
        self.b0 = self.b;
        self.p = CodePtr::Local(LocalCodePtr::DirEntry(p));
    }
}
