use std::collections::BTreeSet;
use std::env;

#[derive(Debug)]
pub struct MachineArgs {
    pub add_history: bool,
}

impl MachineArgs {
    pub fn new() -> Self {
        let args: BTreeSet<String> = env::args().collect();
        Self {
            add_history: !args.contains("--no-add-history"),
        }
    }
}
