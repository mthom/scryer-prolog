#[cfg(rust_version = "1.87.0")]
pub use ge_1_87_0::{PipeReader, PipeWriter};

#[cfg(not(rust_version = "1.87.0"))]
pub use lt_1_87_0::{PipeReader, PipeWriter};

#[cfg(not(rust_version = "1.87.0"))]
pub(crate) use lt_1_87_0::PipeReaderInner;

#[cfg(not(rust_version = "1.87.0"))]
mod lt_1_87_0 {
    use std::process::{ChildStderr, ChildStdout};

    pub type PipeWriter = std::process::ChildStdin;

    #[derive(Debug)]
    pub struct PipeReader(pub(crate) PipeReaderInner);

    #[derive(Debug)]
    pub(crate) enum PipeReaderInner {
        Stdout(ChildStdout),
        Stderr(ChildStderr),
    }

    impl std::io::Read for PipeReader {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            match &mut self.0 {
                PipeReaderInner::Stdout(child_stdout) => child_stdout.read(buf),
                PipeReaderInner::Stderr(child_stderr) => child_stderr.read(buf),
            }
        }

        fn read_vectored(
            &mut self,
            bufs: &mut [std::io::IoSliceMut<'_>],
        ) -> std::io::Result<usize> {
            match &mut self.0 {
                PipeReaderInner::Stdout(child_stdout) => child_stdout.read_vectored(bufs),
                PipeReaderInner::Stderr(child_stderr) => child_stderr.read_vectored(bufs),
            }
        }

        fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize> {
            match &mut self.0 {
                PipeReaderInner::Stdout(child_stdout) => child_stdout.read_to_end(buf),
                PipeReaderInner::Stderr(child_stderr) => child_stderr.read_to_end(buf),
            }
        }

        fn read_to_string(&mut self, buf: &mut String) -> std::io::Result<usize> {
            match &mut self.0 {
                PipeReaderInner::Stdout(child_stdout) => child_stdout.read_to_string(buf),
                PipeReaderInner::Stderr(child_stderr) => child_stderr.read_to_string(buf),
            }
        }

        fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
            match &mut self.0 {
                PipeReaderInner::Stdout(child_stdout) => child_stdout.read_exact(buf),
                PipeReaderInner::Stderr(child_stderr) => child_stderr.read_exact(buf),
            }
        }
    }
}

#[cfg(rust_version = "1.87.0")]
mod ge_1_87_0 {
    pub type PipeReader = std::io::PipeReader;
    pub type PipeWriter = std::io::PipeWriter;
}
