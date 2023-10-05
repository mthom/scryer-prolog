pub struct MachineConfig {
    pub streams: StreamConfig,
    pub toplevel: &'static str,
}

pub enum StreamConfig {
    Stdio,
    Memory,
}

impl Default for MachineConfig {
    fn default() -> Self {
        MachineConfig {
            streams: StreamConfig::Stdio,
            toplevel: include_str!("../toplevel.pl"),
        }
    }
}

impl MachineConfig {
    pub fn in_memory() -> Self {
        MachineConfig {
            streams: StreamConfig::Memory,
            ..Default::default()
        }
    }

    pub fn with_toplevel(mut self, toplevel: &'static str) -> Self {
        self.toplevel = toplevel;
        self
    }
}
