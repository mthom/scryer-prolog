use crate::prolog_parser::ast::*;

use crate::prolog::read::readline::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;
use crate::prolog::read::PrologStream;

use std::cell::RefCell;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::{stdout, Cursor, ErrorKind, Read, Write};
use std::hash::{Hash, Hasher};
use std::net::TcpStream;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StreamType {
    Binary,
    Text,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    InputFile(File),
    OutputFile(File),
    Null,
    ReadlineStream(ReadlineStream),
    // Stdin,
    Stdout,
    TcpStream(TcpStream),
}

impl fmt::Debug for StreamInstance {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &StreamInstance::Bytes(ref bytes) =>
                write!(fmt, "Bytes({:?})", bytes),
            &StreamInstance::DynReadSource(_) =>
                write!(fmt, "DynReadSource(_)"),  // Hacky solution.
            &StreamInstance::InputFile(ref file) => write!(fmt, "InputFile({:?})", file),
            &StreamInstance::OutputFile(ref file) => write!(fmt, "OutputFile({:?})", file),
            &StreamInstance::Null => write!(fmt, "Null"),
            &StreamInstance::ReadlineStream(ref readline_stream) =>
                write!(fmt, "ReadlineStream({:?})", readline_stream),
            // &StreamInstance::Stdin => write!(fmt, "Stdin"),
            &StreamInstance::Stdout => write!(fmt, "Stdout"),
            &StreamInstance::TcpStream(ref tcp_stream) =>
                write!(fmt, "TcpStream({:?})", tcp_stream),
        }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Stream {
    pub options: StreamOptions,
    stream_inst: WrappedStreamInstance,
}

impl From<TcpStream> for Stream {
    fn from(tcp_stream: TcpStream) -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::TcpStream(tcp_stream)
            )
        }
    }
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

impl Stream {
    #[inline]
    pub(crate)
    fn as_ptr(&self) -> *const u8 {
        let rc = self.stream_inst.0.clone();
        let ptr = Rc::into_raw(rc);

        unsafe {
            // must be done to avoid memory leak.
            let _ = Rc::from_raw(ptr);
        }

        ptr as *const u8
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
    fn from_file_as_output(file: File) -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::OutputFile(file)
            ),
        }
    }

    #[inline]
    pub(crate)
    fn from_file_as_input(file: File) -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(
                StreamInstance::InputFile(file)
            ),
        }
    }

/*
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
*/

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
            //StreamInstance::Stdin |
            StreamInstance::ReadlineStream(_) => {
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
            // StreamInstance::Stdin |
            StreamInstance::TcpStream(_) |
            StreamInstance::Bytes(_) |
            StreamInstance::ReadlineStream(_) |
            StreamInstance::DynReadSource(_) |
            StreamInstance::InputFile(_) => {
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
          | StreamInstance::OutputFile(_) => {
                true
           }
            _ => {
                false
            }
        }
    }
}

impl MachineState {
    pub(crate)
    fn to_stream_options(
        &self,
        alias: Addr,
        eof_action: Addr,
        reposition: Addr,
        stream_type: Addr,
    ) -> StreamOptions {
        let alias =
            match self.store(self.deref(alias)) {
                Addr::Con(h) if self.heap.atom_at(h) => {
                    if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                        Some(name.clone())
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    None
                }
            };

        let eof_action =
            match self.store(self.deref(eof_action)) {
                Addr::Con(h) if self.heap.atom_at(h) => {
                    if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                        match name.as_str() {
                            "eof_code" => EOFAction::EOFCode,
                            "error" => EOFAction::Error,
                            "reset" => EOFAction::Reset,
                            _ => unreachable!(),
                        }
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    unreachable!()
                }
            };

        let reposition =
            match self.store(self.deref(reposition)) {
                Addr::Con(h) if self.heap.atom_at(h) => {
                    if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                        name.as_str() == "true"
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    unreachable!()
                }
            };

        let stream_type =
            match self.store(self.deref(stream_type)) {
                Addr::Con(h) if self.heap.atom_at(h) => {
                    if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                        match name.as_str() {
                            "text"   => StreamType::Text,
                            "binary" => StreamType::Binary,
                            _ => unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    unreachable!()
                }
            };

        let mut options = StreamOptions::default();

        options.stream_type = stream_type;
        options.reposition  = reposition;
        options.alias = alias;
        options.eof_action = eof_action;

        options
    }

    pub(crate)
    fn get_stream_or_alias(
        &mut self,
        addr: Addr,
        indices: &IndexStore,
        caller: &'static str,
        arity: usize,
    ) -> Result<Stream, MachineStub>
    {
        Ok(match self.store(self.deref(addr)) {
            Addr::Con(h) if self.heap.atom_at(h) => {
	            if let HeapCellValue::Atom(ref atom, ref spec) = self.heap.clone(h) {
                    match indices.stream_aliases.get(atom) {
                        Some(stream) => {
                            stream.clone()
                        }
                        None => {
                            let stub = MachineError::functor_stub(clause_name!(caller), arity);
                            let h = self.heap.h();

                            let addr = self.heap.to_unifiable(
                                HeapCellValue::Atom(atom.clone(), spec.clone())
                            );

                            return Err(self.error_form(
                                MachineError::existence_error(h + 1, ExistenceError::Stream(addr)),
                                stub,
                            ));
                        }
                    }
                } else {
                    unreachable!()
                }
            }
            Addr::Stream(h) => {
                if let HeapCellValue::Stream(ref stream) = &self.heap[h] {
                    stream.clone()
                } else {
                    unreachable!()
                }
            }
            addr => {
                let stub = MachineError::functor_stub(clause_name!(caller), arity);

                if addr.is_ref() {
                    return Err(self.error_form(
                        MachineError::instantiation_error(),
                        stub,
                    ));
                } else {
                    return Err(self.error_form(
                        MachineError::domain_error(DomainErrorType::StreamOrAlias, addr),
                        stub,
                    ));
                }
            }
        })
    }

    pub(crate)
    fn open_parsing_stream(
        &self,
        stream: Stream,
        stub_name: &'static str,
        stub_arity: usize,
    ) -> Result<PrologStream, MachineStub> {
        match parsing_stream(stream) {
            Ok(stream) => {
                Ok(stream)
            }
            Err(e) => {
                let stub = MachineError::functor_stub(clause_name!(stub_name), stub_arity);
                let err = MachineError::session_error(
                    self.heap.h(),
                    SessionError::from(e),
                );

                Err(self.error_form(err, stub))
            }
        }
    }

    pub(crate)
    fn open_permission_error<T: PermissionError>(
        &self,
        culprit: T,
        stub_name: &'static str,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = MachineError::functor_stub(clause_name!(stub_name), stub_arity);
        let err = MachineError::permission_error(
            self.heap.h(),
            Permission::Open,
            "source_sink",
            culprit,
        );

        return self.error_form(err, stub);
    }

    pub(crate)
    fn occupied_alias_permission_error(
        &self,
        alias: ClauseName,
        stub_name: &'static str,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = MachineError::functor_stub(clause_name!(stub_name), stub_arity);
        let err = MachineError::permission_error(
            self.heap.h(),
            Permission::Open,
            "source_sink",
            functor!("alias", [clause_name(alias)]),
        );

        return self.error_form(err, stub);
    }

    pub(crate)
    fn reposition_error(
        &self,
        stub_name: &'static str,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = MachineError::functor_stub(clause_name!(stub_name), stub_arity);
        let rep_stub = functor!("reposition", [atom("true")]);

        let err = MachineError::permission_error(
            self.heap.h(),
            Permission::Open,
            "source_sink",
            rep_stub,
        );

        return self.error_form(err, stub);
    }
}

impl Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match *self.stream_inst.0.borrow_mut() {
            StreamInstance::InputFile(ref mut file) => {
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
/*
            StreamInstance::Stdin => {
                stdin().read(buf)
            }
*/
            StreamInstance::OutputFile(_) | StreamInstance::Stdout | StreamInstance::Null => {
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
            StreamInstance::OutputFile(ref mut file) => {
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
            StreamInstance::DynReadSource(_) | StreamInstance::ReadlineStream(_) |
            StreamInstance::InputFile(_) | StreamInstance::Null => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::WriteToInputStream,
                ))
            }
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match *self.stream_inst.0.borrow_mut() {
            StreamInstance::OutputFile(ref mut file) => {
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
            StreamInstance::DynReadSource(_) | StreamInstance::ReadlineStream(_) |
            StreamInstance::InputFile(_) | StreamInstance::Null => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::FlushToInputStream,
                ))
            }
        }
    }
}

//TODO: write a Seek instance.
