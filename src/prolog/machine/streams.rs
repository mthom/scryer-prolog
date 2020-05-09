use crate::prolog_parser::ast::*;

use crate::prolog::read::PrologStream;
use crate::prolog::read::readline::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;

use std::cmp::Ordering;
use std::cell::RefCell;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::{stdout, Cursor, ErrorKind, Read, Seek, SeekFrom, Write};
use std::hash::{Hash, Hasher};
use std::net::{Shutdown, TcpStream};
use std::ops::DerefMut;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StreamType {
    Binary,
    Text,
}

impl StreamType {
    #[inline]
    pub(crate)
    fn as_str(&self) -> &'static str {
        match self {
            StreamType::Binary => "binary_stream",
            StreamType::Text => "text_stream",
        }
    }

    #[inline]
    pub(crate)
    fn as_property_str(&self) -> &'static str {
        match self {
            StreamType::Binary => "binary",
            StreamType::Text => "text",
        }
    }

    #[inline]
    pub(crate)
    fn other(self) -> StreamType {
        match self {
            StreamType::Binary => StreamType::Text,
            StreamType::Text => StreamType::Binary,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EOFAction {
    EOFCode,
    Error,
    Reset,
}

pub enum AtEndOfStream {
    Not,
    End,
    Past
}

impl AtEndOfStream {
    #[inline]
    pub(crate)
    fn as_str(&self) -> &'static str {
        match self {
            AtEndOfStream::Not => "not",
            AtEndOfStream::Past => "past",
            AtEndOfStream::End => "end",
        }
    }
}

impl EOFAction {
    #[inline]
    pub(crate)
    fn as_str(&self) -> &'static str {
        match self {
            EOFAction::EOFCode => "eof_code",
            EOFAction::Error => "error",
            EOFAction::Reset => "reset",
        }
    }
}

/* all these streams are closed automatically when the instance is
 * dropped. */
pub enum StreamInstance {
    Bytes(Cursor<Vec<u8>>),
    DynReadSource(Box<dyn Read>),
    InputFile(ClauseName, File),
    OutputFile(ClauseName, File, bool), // File, append.
    Null,
    ReadlineStream(ReadlineStream),
    Stdout,
    TcpStream(ClauseName, TcpStream),
}

impl Drop for StreamInstance {
    fn drop(&mut self) {
        match self {
            StreamInstance::TcpStream(_, ref mut tcp_stream) => {
                tcp_stream.shutdown(Shutdown::Both).unwrap();
            }
            _ => {
            }
        }
    }
}

impl fmt::Debug for StreamInstance {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &StreamInstance::Bytes(ref bytes) =>
                write!(fmt, "Bytes({:?})", bytes),
            &StreamInstance::DynReadSource(_) =>
                write!(fmt, "DynReadSource(_)"),  // Hacky solution.
            &StreamInstance::InputFile(_, ref file) => write!(fmt, "InputFile({:?})", file),
            &StreamInstance::OutputFile(_, ref file, _) => write!(fmt, "OutputFile({:?})", file),
            &StreamInstance::Null => write!(fmt, "Null"),
            &StreamInstance::ReadlineStream(ref readline_stream) =>
                write!(fmt, "ReadlineStream({:?})", readline_stream),
            // &StreamInstance::Stdin => write!(fmt, "Stdin"),
            &StreamInstance::Stdout => write!(fmt, "Stdout"),
            &StreamInstance::TcpStream(_, ref tcp_stream) =>
                write!(fmt, "TcpStream({:?})", tcp_stream),
        }
    }
}

#[derive(Debug, Clone)]
struct WrappedStreamInstance(Rc<RefCell<(bool, StreamInstance)>>);

impl WrappedStreamInstance {
    #[inline]
    fn new(stream_inst: StreamInstance) -> Self {
        WrappedStreamInstance(
            Rc::new(RefCell::new((false, stream_inst)))
        )
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
    PeekByteFailed,
    PeekByteFromNonPeekableStream,
    PeekCharFailed,
    PeekCharFromNonPeekableStream,
    ReadFromOutputStream,
    WriteToInputStream,
    FlushToInputStream,
}

impl fmt::Display for StreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StreamError::PeekByteFailed => {
                write!(f, "peek byte failed!")
            }
            StreamError::PeekByteFromNonPeekableStream => {
                write!(f, "attempted to peek byte from a non-peekable input stream")
            }
            StreamError::PeekCharFailed => {
                write!(f, "peek char failed!")
            }
            StreamError::PeekCharFromNonPeekableStream => {
                write!(f, "attempted to peek char from a non-peekable input stream")
            }
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

#[derive(Debug, Clone, Hash)]
pub struct Stream {
    pub options: StreamOptions,
    stream_inst: WrappedStreamInstance,
}

impl PartialOrd for Stream {
    #[inline]
    fn partial_cmp(&self, other: &Stream) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Stream {
    #[inline]
    fn cmp(&self, other: &Stream) -> Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

impl PartialEq for Stream {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.stream_inst == other.stream_inst
    }
}

impl Eq for Stream {}

impl From<String> for Stream {
    fn from(string: String) -> Self {
        Stream::from_inst(StreamInstance::Bytes(Cursor::new(string.into_bytes())))
    }
}

impl From<ReadlineStream> for Stream {
    fn from(rl_stream: ReadlineStream) -> Self {
        Stream::from_inst(StreamInstance::ReadlineStream(rl_stream))
    }
}

impl From<&'static str> for Stream {
    fn from(src: &'static str) -> Stream {
        Stream::from_inst(StreamInstance::DynReadSource(Box::new(src.as_bytes())))
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
    fn position(&mut self) -> Option<u64> {
        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::InputFile(_, ref mut file) => {
                file.seek(SeekFrom::Current(0)).ok()
            }
            _ => {
                None
            }
        }
    }

    #[inline]
    pub(crate)
    fn set_position(&mut self, position: u64) {
        match self.stream_inst.0.borrow_mut().deref_mut() {
            (past_end_of_stream, StreamInstance::InputFile(_, ref mut file)) => {
                file.seek(SeekFrom::Start(position)).unwrap();

                if let Ok(metadata) = file.metadata() {
                    *past_end_of_stream = position > metadata.len();
                }
            }
            _ => {
            }
        }
    }

    #[inline]
    pub(crate)
    fn past_end_of_stream(&self) -> bool {
        self.stream_inst.0.borrow_mut().0
    }

    #[inline]
    pub(crate)
    fn set_past_end_of_stream(&mut self) {
        self.stream_inst.0.borrow_mut().0 = true;
    }

    #[inline]
    pub(crate)
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        if self.past_end_of_stream() {
            return AtEndOfStream::Past;
        }

        match self.stream_inst.0.borrow_mut().deref_mut() {
            (past_end_of_stream, StreamInstance::InputFile(_, ref mut file)) => {
                match file.metadata() {
                    Ok(metadata) => {
                        if let Ok(position) = file.seek(SeekFrom::Current(0)) {
                            return match position.cmp(&metadata.len()) {
                                Ordering::Equal => {
                                    AtEndOfStream::End
                                }
                                Ordering::Less => {
                                    AtEndOfStream::Not
                                }
                                Ordering::Greater => {
                                    *past_end_of_stream = true; //self.set_past_end_of_stream();
                                    AtEndOfStream::Past
                                }
                            };
                        } else {
                            *past_end_of_stream = true; //self.set_past_end_of_stream();
                            AtEndOfStream::Past
                        }
                    }
                    _ => {
                        *past_end_of_stream = true; //self.set_past_end_of_stream();
                        AtEndOfStream::Past
                    }
                }
            }
            _ => {
                AtEndOfStream::Not
            }
        }
    }

    #[inline]
    pub(crate)
    fn file_name(&self) -> Option<ClauseName> {
        match self.stream_inst.0.borrow().1 {
            StreamInstance::InputFile(ref name, _) => {
                Some(name.clone())
            }
            StreamInstance::OutputFile(ref name, ..) => {
                Some(name.clone())
            }
            StreamInstance::TcpStream(ref name, _) => {
                Some(name.clone())
            }
            _ => {
                None
            }
        }
    }

    #[inline]
    pub(crate)
    fn mode(&self) -> &'static str {
        match self.stream_inst.0.borrow().1 {
            StreamInstance::Bytes(_) |
            StreamInstance::ReadlineStream(_) |
            StreamInstance::DynReadSource(_) |
            StreamInstance::InputFile(..) => {
                "read"
            }
            StreamInstance::TcpStream(..) => {
                "read_append"
            }
            StreamInstance::OutputFile(_, _, true) => {
                "append"
            }
            StreamInstance::Stdout |
            StreamInstance::OutputFile(_, _, false) => {
                "write"
            }
            StreamInstance::Null => {
                ""
            }
        }
    }

    #[inline]
    fn from_inst(stream_inst: StreamInstance) -> Self {
        Stream {
            options: StreamOptions::default(),
            stream_inst: WrappedStreamInstance::new(stream_inst)
        }
    }

    #[inline]
    pub(crate)
    fn stdout() -> Self {
        Stream::from_inst(StreamInstance::Stdout)
    }

    #[inline]
    pub(crate)
    fn from_tcp_stream(address: ClauseName, tcp_stream: TcpStream) -> Self {
        tcp_stream.set_read_timeout(None).unwrap();
        tcp_stream.set_write_timeout(None).unwrap();

        Stream::from_inst(StreamInstance::TcpStream(address, tcp_stream))
    }

    #[inline]
    pub(crate)
    fn from_file_as_output(name: ClauseName, file: File, in_append_mode: bool) -> Self {
        Stream::from_inst(StreamInstance::OutputFile(name, file, in_append_mode))
    }

    #[inline]
    pub(crate)
    fn from_file_as_input(name: ClauseName, file: File) -> Self {
        Stream::from_inst(StreamInstance::InputFile(name, file))
    }

    #[inline]
    pub(crate)
    fn is_stdout(&self) -> bool {
        match self.stream_inst.0.borrow().1 {
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
        match self.stream_inst.0.borrow().1 {
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
    fn close(&mut self) {
        self.stream_inst.0.borrow_mut().1 = StreamInstance::Null;
    }

    #[inline]
    pub(crate)
    fn is_null_stream(&self) -> bool {
        if let StreamInstance::Null = self.stream_inst.0.borrow().1 {
            true
        } else {
            false
        }
    }

    #[inline]
    pub(crate)
    fn is_input_stream(&self) -> bool {
        match self.stream_inst.0.borrow().1 {
            // StreamInstance::Stdin |
            StreamInstance::TcpStream(..) |
            StreamInstance::Bytes(_) |
            StreamInstance::ReadlineStream(_) |
            StreamInstance::DynReadSource(_) |
            StreamInstance::InputFile(..) => {
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
        match self.stream_inst.0.borrow().1 {
            StreamInstance::Stdout
          | StreamInstance::TcpStream(..)
          | StreamInstance::Bytes(_)
          | StreamInstance::OutputFile(..) => {
                true
           }
            _ => {
                false
            }
        }
    }

    // returns true on success.
    #[inline]
    fn reset(&mut self) -> bool {
        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::Bytes(ref mut cursor) => {
                cursor.set_position(0);
                true
            }
            StreamInstance::InputFile(_, ref mut file) => {
                file.seek(SeekFrom::Start(0)).unwrap();
                true
            }
            StreamInstance::ReadlineStream(ref mut stream) => {
                *stream = ReadlineStream::new(String::new());
                true
            }
            _ => {
                false
            }
        }
    }

    #[inline]
    pub(crate)
    fn peek_byte(&mut self) -> std::io::Result<u8> {
        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::Bytes(ref mut cursor) => {
                let mut b = [0u8; 1];
                let pos = cursor.position();

                match cursor.read(&mut b)? {
                    1 => {
                        cursor.set_position(pos);
                        Ok(b[0])
                    }
                    _ => {
                        Err(std::io::Error::new(
                            ErrorKind::UnexpectedEof,
                            "end of file",
                        ))
                    }
                }
            }
            StreamInstance::InputFile(_, ref mut file) => {
                let mut b = [0u8; 1];

                match file.read(&mut b)? {
                    1 => {
                        file.seek(SeekFrom::Current(-1))?;
                        Ok(b[0])
                    }
                    _ => {
                        Err(std::io::Error::new(
                            ErrorKind::UnexpectedEof,
                            StreamError::PeekByteFailed,
                        ))
                    }
                }
            }
            StreamInstance::ReadlineStream(ref mut stream) => {
                stream.peek_byte()
            }
            StreamInstance::TcpStream(_, ref mut tcp_stream) => {
                let mut b = [0u8; 1];
                tcp_stream.peek(&mut b)?;
                Ok(b[0])
            }
            _ => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::PeekByteFromNonPeekableStream,
                ))
            }
        }
    }

    #[inline]
    pub(crate)
    fn peek_char(&mut self) -> std::io::Result<char> {
        use unicode_reader::CodePoints;

        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::InputFile(_, ref mut file) => {
                let c = {
                    let mut iter = CodePoints::from(&*file);

                    if let Some(Ok(c)) = iter.next() {
                        c
                    } else {
                        return Err(std::io::Error::new(
                            ErrorKind::UnexpectedEof,
                            StreamError::PeekCharFailed
                        ));
                    }
                };

                file.seek(SeekFrom::Current(- (c.len_utf8() as i64)))?;

                Ok(c)
            }
            StreamInstance::ReadlineStream(ref mut stream) => {
                stream.peek_char()
            }
            StreamInstance::TcpStream(_, ref tcp_stream) => {
                let c = {
                    let mut buf = [0u8; 8];
                    tcp_stream.peek(&mut buf)?;

                    let mut iter = CodePoints::from(buf.bytes());

                    if let Some(Ok(c)) = iter.next() {
                        c
                    } else {
                        return Err(std::io::Error::new(
                            ErrorKind::UnexpectedEof,
                            StreamError::PeekCharFailed
                        ));
                    }
                };

                Ok(c)
            }
            _ => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::PeekCharFromNonPeekableStream,
                ))
            }
        }
    }
}

impl MachineState {
    #[inline]
    pub(crate)
    fn eof_action(
        &mut self,
        result: Addr,
        stream: &mut Stream,
        caller: ClauseName,
        arity: usize,
    ) -> CallResult {
        match stream.options.eof_action {
            EOFAction::Error => {
                stream.set_past_end_of_stream();
                return Err(self.open_past_eos_error(stream.clone(), caller, arity));
            }
            EOFAction::EOFCode => {
                let end_of_stream = self.heap.to_unifiable(
                    HeapCellValue::Atom(clause_name!("end_of_file"), None)
                );

                stream.set_past_end_of_stream();
                Ok(self.unify(result, end_of_stream))
            }
            EOFAction::Reset => {
                if !stream.reset() {
                    stream.set_past_end_of_stream();
                }

                Ok(self.fail = stream.past_end_of_stream())
            }
        }
    }

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
                        Some(stream) if !stream.is_null_stream() => {
                            stream.clone()
                        }
                        _ => {
                            let stub = MachineError::functor_stub(clause_name!(caller), arity);

                            let addr = self.heap.to_unifiable(
                                HeapCellValue::Atom(atom.clone(), spec.clone())
                            );

                            return Err(self.error_form(
                                MachineError::existence_error(self.heap.h(), ExistenceError::Stream(addr)),
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
                    if stream.is_null_stream() {
                        return Err(self.open_permission_error(
                            Addr::Stream(h),
                            caller,
                            arity,
                        ));
                    } else {
                        stream.clone()
                    }
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
        match parsing_stream(stream.clone()) {
            Ok(parsing_stream) => {
                Ok(parsing_stream)
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
    fn stream_permission_error(
        &self,
        perm: Permission,
        err_string: &'static str,
        stream: Stream,
        caller: ClauseName,
        arity: usize,
    ) -> MachineStub {
        let stub = MachineError::functor_stub(caller, arity);
        let payload = vec![
            HeapCellValue::Stream(stream)
        ];

        let err = MachineError::permission_error(
            self.heap.h(),
            perm,
            err_string,
            payload,
        );

        return self.error_form(err, stub);
    }

    #[inline]
    pub(crate)
    fn open_past_eos_error(
        &self,
        stream: Stream,
        caller: ClauseName,
        arity: usize,
    ) -> MachineStub {
        self.stream_permission_error(
            Permission::InputStream,
            "past_end_of_stream",
            stream,
            caller,
            arity,
        )
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


    pub(crate)
    fn check_stream_properties(
        &mut self,
        stream: &mut Stream,
        expected_type: StreamType,
        input: Option<Addr>,
        caller: ClauseName,
        arity: usize,
    ) -> CallResult {
        let opt_err =
            if input.is_some() && !stream.is_input_stream() {
                Some("stream") // 8.14.2.3 g)
            } else if input.is_none() && !stream.is_output_stream() {
                Some("stream") // 8.14.2.3 g)
            } else if stream.options.stream_type != expected_type {
                Some(expected_type.other().as_str()) // 8.14.2.3 h)
            } else {
                None
            };

        let permission =
            if input.is_some() { Permission::InputStream } else { Permission::OutputStream };

        if let Some(err_string) = opt_err {
            return Err(self.stream_permission_error(
                permission,
                err_string,
                stream.clone(),
                caller,
                arity,
            ));
        }

        if let Some(input) = input {
            if stream.past_end_of_stream() {
                self.eof_action(
                    input,
                    stream,
                    caller,
                    arity,
                )?;
            }
        }

        Ok(())
    }
}

impl Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::InputFile(_, ref mut file) => {
                file.read(buf)
            }
            StreamInstance::TcpStream(_, ref mut tcp_stream) => {
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
            StreamInstance::OutputFile(..) | StreamInstance::Stdout | StreamInstance::Null => {
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
        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::OutputFile(_, ref mut file, _) => {
                file.write(buf)
            }
            StreamInstance::TcpStream(_, ref mut tcp_stream) => {
                tcp_stream.write(buf)
            }
            StreamInstance::Bytes(ref mut cursor) => {
                cursor.write(buf)
            }
            StreamInstance::Stdout => {
                stdout().write(buf)
            }
            StreamInstance::DynReadSource(_) | StreamInstance::ReadlineStream(_) |
            StreamInstance::InputFile(..) | StreamInstance::Null => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::WriteToInputStream,
                ))
            }
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self.stream_inst.0.borrow_mut().1 {
            StreamInstance::OutputFile(_, ref mut file, _) => {
                file.flush()
            }
            StreamInstance::TcpStream(_, ref mut tcp_stream) => {
                tcp_stream.flush()
            }
            StreamInstance::Bytes(ref mut cursor) => {
                cursor.flush()
            }
            StreamInstance::Stdout => {
                stdout().flush()
            }
            StreamInstance::DynReadSource(_) | StreamInstance::ReadlineStream(_) |
            StreamInstance::InputFile(..) | StreamInstance::Null => {
                Err(std::io::Error::new(
                    ErrorKind::PermissionDenied,
                    StreamError::FlushToInputStream,
                ))
            }
        }
    }
}
