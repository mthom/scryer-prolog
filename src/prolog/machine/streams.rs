use crate::prolog_parser::ast::*;

use crate::prolog::read::readline::*;

use std::cell::RefCell;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::{stdin, stdout, Cursor, ErrorKind, Read, Write};
use std::hash::{Hash, Hasher};
use std::net::TcpStream;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum StreamType {
    Binary,
    Text,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum EOFAction {
    EOFCode,
    Error,
    Reset,
}

/* all these streams are closed automatically when the instance is
 * dropped. */
pub enum StreamInstance {
    Bytes(Cursor<Vec<u8>>),
    DynReadSource(Box<dyn Read>),
    File(File),
    Null,
    ReadlineStream(ReadlineStream),
    Stdin,
    Stdout,
    TcpStream(TcpStream),
}

#[derive(Clone)]
struct WrappedStreamInstance(Rc<RefCell<StreamInstance>>);

impl WrappedStreamInstance {
    #[inline]
    fn new(stream_inst: StreamInstance) -> Self {
        WrappedStreamInstance(Rc::new(RefCell::new(stream_inst)))
    }
}

impl PartialEq for WrappedStreamInstance {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for WrappedStreamInstance {}

impl Hash for WrappedStreamInstance {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let rc = &self.0;
        let ptr = Rc::into_raw(rc.clone());

        state.write_usize(ptr as usize);

        unsafe {
            // necessary to avoid memory leak.
            let _ = Rc::from_raw(ptr);
        };
    }
}

#[derive(Debug)]
enum StreamError {
    ReadFromOutputStream,
    WriteToInputStream,
    FlushToInputStream,
}

impl fmt::Display for StreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StreamError::ReadFromOutputStream => {
                write!(f, "attempted to read from a write-only stream")
            }
            StreamError::WriteToInputStream => {
                write!(f, "attempted to write to a read-only stream")
            }
            StreamError::FlushToInputStream => {
                write!(f, "attempted to flush a read-only stream")
            }
        }
    }
}

impl Error for StreamError {}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct StreamOptions {
    pub stream_type: StreamType,
    pub reposition: bool,
    pub alias: Option<ClauseName>,
    pub eof_action: EOFAction,
}

impl Default for StreamOptions {
    #[inline]
    fn default() -> Self {
        StreamOptions {
            stream_type: StreamType::Text,
            reposition: false,
            alias: None,
            eof_action: EOFAction::EOFCode,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Stream {
    pub options: StreamOptions,
    stream_inst: WrappedStreamInstance,
}

impl From<String> for Stream {
    fn from(string: String) -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::Bytes(Cursor::new(string.into_bytes()))
            )
        }
    }
}

impl From<ReadlineStream> for Stream {
    fn from(rl_stream: ReadlineStream) -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::ReadlineStream(rl_stream)
            ),
        }
    }
}

impl From<&'static str> for Stream {
    fn from(src: &'static str) -> Stream {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::DynReadSource(Box::new(src.as_bytes()))
            ),
        }
    }
}

impl From<File> for Stream {
    fn from(file: File) -> Stream {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::File(file)
            ),
        }
    }
}

impl Stream {
    #[inline]
    pub(crate)
    fn as_ptr(&self) -> *const RefCell<StreamInstance> {
        let rc = self.stream_inst.0.clone();
        let ptr = Rc::into_raw(rc);

        unsafe {
            // must be done to avoid memory leak.
            let _ = Rc::from_raw(ptr);
        }

        ptr
    }

    #[inline]
    pub(crate)
    fn stdout() -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::Stdout
            ),
        }
    }

    #[inline]
    pub(crate)
    fn stdin() -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::Stdin
            ),
        }
    }

    #[inline]
    pub(crate)
    fn null_stream() -> Self {
        Stream {
            options: StreamOptions::default(), // TODO: null_options?
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::Null
            ),
        }
    }

    #[inline]
    pub(crate)
    fn is_stdout(&self) -> bool {
        match *self.stream_inst.0.borrow() {
            StreamInstance::Stdout => {
                true
            }
            _ => {
                false
            }
        }
    }

    #[inline]
    pub(crate)
    fn is_stdin(&self) -> bool {
        match *self.stream_inst.0.borrow() {
            StreamInstance::Stdin | StreamInstance::ReadlineStream(_) => {
                true
            }
            _ => {
                false
            }
        }
    }

    #[inline]
    pub(crate)
    fn is_input_stream(&self) -> bool {
        match *self.stream_inst.0.borrow() {
            StreamInstance::Stdin
          | StreamInstance::TcpStream(_)
          | StreamInstance::Bytes(_)
          | StreamInstance::ReadlineStream(_)
          | StreamInstance::DynReadSource(_)
          | StreamInstance::File(_) => {
                true
           }
            _ => {
                false
            }
        }
    }

    #[inline]
    pub(crate)
    fn is_output_stream(&self) -> bool {
        match *self.stream_inst.0.borrow() {
            StreamInstance::Stdout
          | StreamInstance::TcpStream(_)
          | StreamInstance::Bytes(_)
          | StreamInstance::File(_) => {
                true
           }
            _ => {
                false
            }
        }
    }
}

impl Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match *self.stream_inst.0.borrow_mut() {
            StreamInstance::File(ref mut file) => {
                file.read(buf)
            }
            StreamInstance::TcpStream(ref mut tcp_stream) => {
                tcp_stream.read(buf)
            }
            StreamInstance::ReadlineStream(ref mut rl_stream) => {
                rl_stream.read(buf)
            }
            StreamInstance::DynReadSource(ref mut src) => {
                src.read(buf)
            }
            StreamInstance::Bytes(ref mut cursor) => {
                cursor.read(buf)
            }
            StreamInstance::Stdin => {
                stdin().read(buf)
            }
            StreamInstance::Stdout | StreamInstance::Null => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::ReadFromOutputStream,
                ))
            }
        }
    }
}

impl Write for Stream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match *self.stream_inst.0.borrow_mut() {
            StreamInstance::File(ref mut file) => {
                file.write(buf)
            }
            StreamInstance::TcpStream(ref mut tcp_stream) => {
                tcp_stream.write(buf)
            }
            StreamInstance::Bytes(ref mut cursor) => {
                cursor.write(buf)
            }
            StreamInstance::Stdout => {
                stdout().write(buf)
            }
            _ => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::WriteToInputStream,
                ))
            }
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match *self.stream_inst.0.borrow_mut() {
            StreamInstance::File(ref mut file) => {
                file.flush()
            }
            StreamInstance::TcpStream(ref mut tcp_stream) => {
                tcp_stream.flush()
            }
            StreamInstance::Bytes(ref mut cursor) => {
                cursor.flush()
            }
            StreamInstance::Stdout => {
                stdout().flush()
            }
            _ => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::FlushToInputStream,
                ))
            }
        }
    }
}

//TODO: write a Seek instance.
