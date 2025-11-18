use std::env;

#[derive(Debug)]
pub struct MachineArgs {
    pub add_history: bool,
}

impl MachineArgs {
    pub fn new() -> Self {
        Self {
            add_history: env::args().all(|arg| arg != "--no-add-history"),
        }
    }
}

impl Default for MachineArgs {
    fn default() -> Self {
        Self::new()
    }
}
