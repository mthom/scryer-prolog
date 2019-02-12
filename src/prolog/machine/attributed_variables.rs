use prolog::machine::*;

pub static VERIFY_ATTRS: &str = include_str!("attributed_variables.pl");

pub(super) type Bindings = Vec<(usize, Addr)>;

pub(super) struct AttrVarInitializer {    
    pub(super) bindings: Bindings,
    pub(super) cp: LocalCodePtr,
    pub(super) verify_attrs_loc: usize
}

impl AttrVarInitializer {
    pub(super) fn new(p: usize) -> Self {
        AttrVarInitializer {
            bindings: vec![],
            cp: LocalCodePtr::default(),
            verify_attrs_loc: p,
        }
    }

    #[inline]
    pub(super) fn reset(&mut self) {
        self.bindings.clear();
    }
}

impl MachineState {
    pub(super) fn push_attr_var_binding(&mut self, h: usize, addr: Addr)
    {
        if self.attr_var_init.bindings.is_empty() {
            self.attr_var_init.cp = self.p.local() + 1;
            self.p = CodePtr::VerifyAttrInterrupt(self.attr_var_init.verify_attrs_loc);
        }

        self.attr_var_init.bindings.push((h, addr));
    }

    fn populate_var_and_value_lists(&mut self) -> (Addr, Addr) {
        let iter = self.attr_var_init.bindings.iter().map(|(ref h, _)| Addr::AttrVar(*h));
        let var_list_addr = Addr::HeapCell(self.heap.to_list(iter));

        let iter = self.attr_var_init.bindings.iter().map(|(_, ref addr)| addr.clone());
        let value_list_addr = Addr::HeapCell(self.heap.to_list(iter));

        (var_list_addr, value_list_addr)
    }

    pub(super)
    fn calculate_register_threshold(&self) -> usize {
        let mut count = 0;
        
        for r in 1 .. MAX_ARITY + 1 {
            if let &Addr::HeapCell(0) = &self[RegType::Temp(r)] {
                break;
            }

            count += 1;
        }

        count
    }
    
    pub(super)
    fn verify_attributes(&mut self)
    {
        /* STEP 1: Undo bindings in machine.
           STEP 2: Write the list of bindings to two lists in the heap, one for vars, one for values.
           STEP 3: Pass the addresses of the lists to iterate in the attr_vars special form.
                   Call verify_attributes/3 wherever applicable.
           STEP 4: Redo the bindings.
           STEP 5: Call the goals.
           STEP 6: Pop the top of AttrVarInitializer::cp_stack to self.p.
           STEP 7: Swap the AttrVarInitializer's Registers back for the machine's Registers.
         */

        // STEP 1.
        for (h, _) in &self.attr_var_init.bindings {
            self.heap[*h] = HeapCellValue::Addr(Addr::AttrVar(*h));
        }

        // STEP 2.
        let (var_list_addr, value_list_addr) = self.populate_var_and_value_lists();

        // STEP 3.
        self[temp_v!(1)] = var_list_addr;
        self[temp_v!(2)] = value_list_addr;
    }
}
