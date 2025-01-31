use std::borrow::Cow;
use std::io::Write;
use std::sync::mpsc::{channel, Receiver, Sender};

use rand::{rngs::StdRng, SeedableRng};

use crate::Machine;

use super::{
    bootstrapping_compile, current_dir, import_builtin_impls, libraries, load_module, Arena, Atom,
    Callback, CompilationTarget, IndexStore, ListingSource, MachineArgs, MachineState, Stream,
    StreamOptions,
};

#[derive(Default)]
enum OutputStreamConfigInner {
    #[default]
    Null,
    Memory,
    Stdout,
    Stderr,
    Callback(Callback),
}

impl std::fmt::Debug for OutputStreamConfigInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "Null"),
            Self::Memory => write!(f, "Memory"),
            Self::Stdout => write!(f, "Stdout"),
            Self::Stderr => write!(f, "Stderr"),
            Self::Callback(_) => f.debug_tuple("Callback").field(&"<callback>").finish(),
        }
    }
}

/// Configuration for an output stream.
#[derive(Debug, Default)]
pub struct OutputStreamConfig {
    inner: OutputStreamConfigInner,
}

impl OutputStreamConfig {
    /// Ignores all output.
    pub fn null() -> Self {
        Self {
            inner: OutputStreamConfigInner::Null,
        }
    }
    /// Sends output to stdout.
    pub fn stdout() -> Self {
        Self {
            inner: OutputStreamConfigInner::Stdout,
        }
    }
    /// Sends output to stderr.
    pub fn stderr() -> Self {
        Self {
            inner: OutputStreamConfigInner::Stderr,
        }
    }
    /// Keeps output in a memory buffer.
    pub fn memory() -> Self {
        Self {
            inner: OutputStreamConfigInner::Memory,
        }
    }
    /// Calls a callback with the output whenever the stream is written to.
    pub fn callback(callback: Callback) -> Self {
        Self {
            inner: OutputStreamConfigInner::Callback(callback),
        }
    }

    fn into_stream(self, arena: &mut Arena) -> Stream {
        match self.inner {
            OutputStreamConfigInner::Null => Stream::Null(StreamOptions::default()),
            OutputStreamConfigInner::Memory => Stream::from_owned_string("".to_owned(), arena),
            OutputStreamConfigInner::Stdout => Stream::stdout(arena),
            OutputStreamConfigInner::Stderr => Stream::stderr(arena),
            OutputStreamConfigInner::Callback(callback) => Stream::from_callback(callback, arena),
        }
    }
}

#[derive(Debug, Default)]
enum InputStreamConfigInner {
    #[default]
    Null,
    Stdin,
    Channel(Receiver<Vec<u8>>),
}

/// Configuration for an input stream;
#[derive(Debug, Default)]
pub struct InputStreamConfig {
    inner: InputStreamConfigInner,
}

impl InputStreamConfig {
    /// Ignores all input.
    pub fn null() -> Self {
        Self {
            inner: InputStreamConfigInner::Null,
        }
    }
    /// Gets input from stdin.
    pub fn stdin() -> Self {
        Self {
            inner: InputStreamConfigInner::Stdin,
        }
    }
    /// Connects the input to the receiving end of a channel.
    pub fn channel() -> (UserInput, Self) {
        let (sender, receiver) = channel();
        (
            UserInput { inner: sender },
            Self {
                inner: InputStreamConfigInner::Channel(receiver),
            },
        )
    }

    fn into_stream(self, arena: &mut Arena, add_history: bool) -> Stream {
        match self.inner {
            InputStreamConfigInner::Null => Stream::Null(StreamOptions::default()),
            InputStreamConfigInner::Stdin => Stream::stdin(arena, add_history),
            InputStreamConfigInner::Channel(channel) => Stream::input_channel(channel, arena),
        }
    }
}

/// Describes how the streams of a [`Machine`](crate::Machine) will be handled.
pub struct StreamConfig {
    /// The configuration for the stdin of the [`Machine`](crate::Machine).
    pub stdin: InputStreamConfig,
    /// The configuration for the stdout of the [`Machine`](crate::Machine).
    pub stdout: OutputStreamConfig,
    /// The configuration for the stderr of the [`Machine`](crate::Machine).
    pub stderr: OutputStreamConfig,
}

impl Default for StreamConfig {
    fn default() -> Self {
        Self::in_memory()
    }
}

impl StreamConfig {
    /// Binds the input, output and error streams to stdin, stdout and stderr.
    pub fn stdio() -> Self {
        StreamConfig {
            stdin: InputStreamConfig::stdin(),
            stdout: OutputStreamConfig::stdout(),
            stderr: OutputStreamConfig::stderr(),
        }
    }

    /// Binds the output stream to a memory buffer, and the error stream to stderr.
    ///
    /// The input stream is ignored.
    pub fn in_memory() -> Self {
        StreamConfig {
            stdin: InputStreamConfig::null(),
            stdout: OutputStreamConfig::memory(),
            stderr: OutputStreamConfig::stderr(),
        }
    }

    /// Calls the given callbacks when the respective streams are written to.
    ///
    /// This also returns a handler to the stdin do the [`Machine`](crate::Machine).
    pub fn with_callbacks(stdout: Option<Callback>, stderr: Option<Callback>) -> (UserInput, Self) {
        let (user_input, channel_stream) = InputStreamConfig::channel();
        (
            user_input,
            StreamConfig {
                stdin: channel_stream,
                stdout: stdout.map_or_else(OutputStreamConfig::null, OutputStreamConfig::callback),
                stderr: stderr.map_or_else(OutputStreamConfig::null, OutputStreamConfig::callback),
            },
        )
    }

    fn into_streams(self, arena: &mut Arena, add_history: bool) -> (Stream, Stream, Stream) {
        (
            self.stdin.into_stream(arena, add_history),
            self.stdout.into_stream(arena),
            self.stderr.into_stream(arena),
        )
    }
}

/// A handler for the stdin of the [`Machine`](crate::Machine).
#[derive(Debug)]
pub struct UserInput {
    inner: Sender<Vec<u8>>,
}

impl Write for UserInput {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.inner
            .send(buf.into())
            .map(|_| buf.len())
            .map_err(|_| std::io::ErrorKind::BrokenPipe.into())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Describes how a [`Machine`](crate::Machine) will be configured.
pub struct MachineBuilder {
    pub(crate) streams: StreamConfig,
    pub(crate) toplevel: Cow<'static, str>,
}

impl Default for MachineBuilder {
    /// Defaults to using in-memory streams.
    fn default() -> Self {
        MachineBuilder {
            streams: Default::default(),
            toplevel: default_toplevel().into(),
        }
    }
}

impl MachineBuilder {
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
    pub fn with_toplevel(mut self, toplevel: impl Into<Cow<'static, str>>) -> Self {
        self.toplevel = toplevel.into();
        self
    }

    /// Builds the [`Machine`](crate::Machine) from this configuration.
    pub fn build(self) -> Machine {
        let args = MachineArgs::new();
        let mut machine_st = MachineState::new();

        let (user_input, user_output, user_error) = self
            .streams
            .into_streams(&mut machine_st.arena, args.add_history);

        let mut wam = Machine {
            machine_st,
            indices: IndexStore::new(),
            code: vec![],
            user_input,
            user_output,
            user_error,
            load_contexts: vec![],
            #[cfg(feature = "ffi")]
            foreign_function_table: Default::default(),
            rng: StdRng::from_entropy(),
        };

        let mut lib_path = current_dir();

        lib_path.pop();
        lib_path.push("lib");

        wam.add_impls_to_indices();

        bootstrapping_compile(
            Stream::from_static_string(
                libraries::get("ops_and_meta_predicates")
                    .expect("library ops_and_meta_predicates should exist"),
                &mut wam.machine_st.arena,
            ),
            &mut wam,
            ListingSource::from_file_and_path(
                atom!("ops_and_meta_predicates.pl"),
                lib_path.clone(),
            ),
        )
        .unwrap();

        bootstrapping_compile(
            Stream::from_static_string(
                libraries::get("builtins").expect("library builtins should exist"),
                &mut wam.machine_st.arena,
            ),
            &mut wam,
            ListingSource::from_file_and_path(atom!("builtins.pl"), lib_path.clone()),
        )
        .unwrap();

        if let Some(builtins) = wam.indices.modules.get_mut(&atom!("builtins")) {
            load_module(
                &mut wam.machine_st,
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                builtins,
            );

            import_builtin_impls(&wam.indices.code_dir, builtins);
        } else {
            unreachable!()
        }

        lib_path.pop(); // remove the "lib" at the end

        bootstrapping_compile(
            Stream::from_static_string(include_str!("../loader.pl"), &mut wam.machine_st.arena),
            &mut wam,
            ListingSource::from_file_and_path(atom!("loader.pl"), lib_path.clone()),
        )
        .unwrap();

        wam.configure_modules();

        if let Some(loader) = wam.indices.modules.get(&atom!("loader")) {
            load_module(
                &mut wam.machine_st,
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                loader,
            );
        } else {
            unreachable!()
        }

        wam.load_special_forms();
        wam.load_top_level(self.toplevel);
        wam.configure_streams();

        wam
    }
}

/// Returns a static string slice to the default toplevel
pub fn default_toplevel() -> &'static str {
    include_str!("../toplevel.pl")
}
