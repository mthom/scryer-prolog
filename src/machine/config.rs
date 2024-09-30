/// Describes how the streams of a [`Machine`](crate::Machine) will be handled.
///
/// Defaults to using standard IO.
pub struct StreamConfig {
    pub(crate) inner: StreamConfigInner,
}

impl Default for StreamConfig {
    fn default() -> Self {
        Self::stdio()
    }
}

impl StreamConfig {
    /// Binds the input, output and error streams to stdin, stdout and stderr.
    pub fn stdio() -> Self {
        StreamConfig {
            inner: StreamConfigInner::Stdio,
        }
    }

    /// Binds the output stream to a memory buffer, and the error stream to stderr.
    ///
    /// The input stream is ignored.
    pub fn in_memory() -> Self {
        StreamConfig {
            inner: StreamConfigInner::Memory,
        }
    }
}

pub(crate) enum StreamConfigInner {
    Stdio,
    Memory,
}

/// Describes how a [`Machine`](crate::Machine) will be configured.
pub struct MachineConfig {
    pub(crate) streams: StreamConfig,
    pub(crate) toplevel: &'static str,
}

impl Default for MachineConfig {
    fn default() -> Self {
        MachineConfig {
            streams: Default::default(),
            toplevel: default_toplevel(),
        }
    }
}

impl MachineConfig {
    /// Creates a default configuration.
    pub fn new() -> Self {
        Default::default()
    }

    /// Uses the given `crate::StreamConfig` in this configuration.
    pub fn with_streams(mut self, streams: StreamConfig) -> Self {
        self.streams = streams;
        self
    }

    /// Uses the given toplevel in this configuration.
    pub fn with_toplevel(mut self, toplevel: &'static str) -> Self {
        self.toplevel = toplevel;
        self
    }
}

/// Returns a static string slice to the default toplevel
pub fn default_toplevel() -> &'static str {
    include_str!("../toplevel.pl")
}
