use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;
use crate::parser::char_reader::*;
use crate::read::*;

use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::types::*;

pub use modular_bitfield::prelude::*;

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::fmt::Debug;
use std::fs::{File, OpenOptions};
use std::hash::{Hash};
use std::io;
use std::io::{BufRead, Cursor, ErrorKind, Read, Seek, SeekFrom, Write};
use std::mem;
use std::net::{TcpStream, Shutdown};
use std::ops::{Deref, DerefMut};
use std::ptr;

use native_tls::TlsStream;
use hyper::body::{Bytes, Sender};

#[derive(Debug, BitfieldSpecifier, Clone, Copy, PartialEq, Eq, Hash)]
#[bits = 1]
pub enum StreamType {
    Binary,
    Text,
}

impl StreamType {
    #[inline]
    pub(crate) fn as_atom(&self) -> Atom {
        match self {
            StreamType::Binary => atom!("binary_stream"),
            StreamType::Text => atom!("text_stream"),
        }
    }

    #[inline]
    pub(crate) fn as_property_atom(&self) -> Atom {
        match self {
            StreamType::Binary => atom!("binary"),
            StreamType::Text => atom!("text"),
        }
    }

    #[inline]
    pub(crate) fn other(self) -> StreamType {
        match self {
            StreamType::Binary => StreamType::Text,
            StreamType::Text => StreamType::Binary,
        }
    }
}

#[derive(Debug, BitfieldSpecifier, Clone, Copy, PartialEq, Eq, Hash)]
#[bits = 2]
pub enum EOFAction {
    EOFCode,
    Error,
    Reset,
}

#[derive(Debug, BitfieldSpecifier, Copy, Clone, PartialEq)]
#[bits = 2]
pub(crate) enum AtEndOfStream {
    Not,
    At,
    Past,
}

impl AtEndOfStream {
    #[inline]
    pub(crate) fn as_atom(&self) -> Atom {
        match self {
            AtEndOfStream::Not => atom!("not"),
            AtEndOfStream::Past => atom!("past"),
            AtEndOfStream::At => atom!("at"),
        }
    }
}

impl EOFAction {
    #[inline]
    pub(crate) fn as_atom(&self) -> Atom {
        match self {
            EOFAction::EOFCode => atom!("eof_code"),
            EOFAction::Error => atom!("error"),
            EOFAction::Reset => atom!("reset"),
        }
    }
}

#[derive(Debug)]
pub struct ByteStream(Cursor<Vec<u8>>);

impl ByteStream {
    #[inline(always)]
    pub fn from_string(string: String) -> Self {
        ByteStream(Cursor::new(string.into()))
    }
}

impl Read for ByteStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}

impl Write for ByteStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let pos = self.0.position();

        self.0.seek(SeekFrom::End(0))?;
        let result = self.0.write(buf);
        self.0.seek(SeekFrom::Start(pos))?;

        result
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

#[derive(Debug)]
pub struct InputFileStream {
    file_name: Atom,
    file: File,
}

impl Read for InputFileStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.file.read(buf)
    }
}

impl StreamLayout<CharReader<InputFileStream>> {
    #[inline]
    fn position(&mut self) -> Option<u64> {
        // stream is the internal CharReader. subtract
        // its pending buffer length from position.
        self.get_mut().file.seek(SeekFrom::Current(0))
            .map(|pos| pos  - self.stream.rem_buf_len() as u64)
            .ok()
    }
}

#[derive(Debug)]
pub struct OutputFileStream {
    file_name: Atom,
    file: File,
    is_append: bool,
}

impl Write for OutputFileStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.file.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        self.file.flush()
    }
}

#[derive(Debug)]
pub struct StaticStringStream {
    stream: Cursor<&'static str>,
}

impl Read for StaticStringStream {
    #[inline(always)]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.stream.read(buf)
    }
}

impl CharRead for StaticStringStream {
    #[inline(always)]
    fn peek_char(&mut self) -> Option<std::io::Result<char>> {
        let pos = self.stream.position() as usize;
        self.stream.get_ref()[pos ..].chars().next().map(Ok)
    }

    #[inline(always)]
    fn consume(&mut self, nread: usize) {
        self.stream.seek(SeekFrom::Current(nread as i64)).unwrap();
    }

    #[inline(always)]
    fn put_back_char(&mut self, c: char) {
        self.stream.seek(SeekFrom::Current(- (c.len_utf8() as i64))).unwrap();
    }
}

#[derive(Debug)]
pub struct NamedTcpStream {
    address: Atom,
    tcp_stream: TcpStream,
}

impl Read for NamedTcpStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.tcp_stream.read(buf)
    }
}

impl Write for NamedTcpStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.tcp_stream.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        self.tcp_stream.flush()
    }
}

#[derive(Debug)]
pub struct NamedTlsStream {
    address: Atom,
    tls_stream: TlsStream<Stream>,
}

impl Read for NamedTlsStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.tls_stream.read(buf)
    }
}

impl Write for NamedTlsStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.tls_stream.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        self.tls_stream.flush()
    }
}

pub struct HttpReadStream {
    url: Atom,
    body_reader: Box<dyn BufRead>,
}

impl Debug for HttpReadStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Http Read Stream [{}]", self.url.as_str())
    }
}

impl Read for HttpReadStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.body_reader.read(buf)
    }
}

pub struct HttpWriteStream {
    body_writer: Sender,
}

impl Debug for HttpWriteStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	write!(f, "Http Write Stream")
    }
}

impl Write for HttpWriteStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
	let bytes = Bytes::copy_from_slice(buf);
	let len = bytes.len();
	match self.body_writer.try_send_data(bytes) {
	    Ok(()) => Ok(len),
	    Err(_) => Err(std::io::Error::from(ErrorKind::Interrupted))
	}
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
	Ok(())
    }
}

#[derive(Debug)]
pub struct StandardOutputStream {}

impl Write for StandardOutputStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        io::stdout().write(buf)
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        io::stdout().flush()
    }
}

#[derive(Debug)]
pub struct StandardErrorStream {}

impl Write for StandardErrorStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        io::stderr().write(buf)
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        io::stderr().flush()
    }
}

#[bitfield]
#[repr(u64)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct StreamOptions {
    pub stream_type: StreamType,
    pub reposition: bool,
    pub eof_action: EOFAction,
    pub has_alias: bool,
    pub alias: B59,
}

impl StreamOptions {
    #[inline]
    pub fn get_alias(self) -> Option<Atom> {
        if self.has_alias() {
            Some(Atom::from((self.alias() << 3) as usize))
        } else {
            None
        }
    }

    #[inline]
    pub fn set_alias_to_atom_opt(&mut self, alias: Option<Atom>) {
        self.set_has_alias(alias.is_some());

        if let Some(alias) = alias {
            self.set_alias(alias.flat_index());
        }
    }
}

impl Default for StreamOptions {
    #[inline]
    fn default() -> Self {
        StreamOptions::new()
            .with_stream_type(StreamType::Text)
            .with_reposition(false)
            .with_eof_action(EOFAction::EOFCode)
            .with_has_alias(false)
            .with_alias(0)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct StreamLayout<T> {
    pub options: StreamOptions,
    pub lines_read: usize,
    past_end_of_stream: bool,
    stream: T,
}

impl<T> StreamLayout<T> {
    #[inline]
    pub fn new(stream: T) -> Self {
        Self {
            options: StreamOptions::default(),
            lines_read: 0,
            past_end_of_stream: false,
            stream,
        }
    }
}

impl<T> Deref for StreamLayout<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.stream
    }
}

impl<T> DerefMut for StreamLayout<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.stream
    }
}

macro_rules! arena_allocated_impl_for_stream {
    ($stream_type:ty, $stream_tag:ident) => {
        impl ArenaAllocated for StreamLayout<$stream_type> {
            type PtrToAllocated = TypedArenaPtr<StreamLayout<$stream_type>>;

            #[inline]
            fn tag() -> ArenaHeaderTag {
                ArenaHeaderTag::$stream_tag
            }

            #[inline]
            fn size(&self) -> usize {
                mem::size_of::<StreamLayout<$stream_type>>()
            }

            #[inline]
            fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
                unsafe {
                    ptr::write(dst, self);
                    TypedArenaPtr::new(dst as *mut Self)
                }
            }
        }
    };
}

arena_allocated_impl_for_stream!(CharReader<ByteStream>, ByteStream);
arena_allocated_impl_for_stream!(CharReader<InputFileStream>, InputFileStream);
arena_allocated_impl_for_stream!(OutputFileStream, OutputFileStream);
arena_allocated_impl_for_stream!(CharReader<NamedTcpStream>, NamedTcpStream);
arena_allocated_impl_for_stream!(CharReader<NamedTlsStream>, NamedTlsStream);
arena_allocated_impl_for_stream!(CharReader<HttpReadStream>, HttpReadStream);
arena_allocated_impl_for_stream!(CharReader<HttpWriteStream>, HttpWriteStream);
arena_allocated_impl_for_stream!(ReadlineStream, ReadlineStream);
arena_allocated_impl_for_stream!(StaticStringStream, StaticStringStream);
arena_allocated_impl_for_stream!(StandardOutputStream, StandardOutputStream);
arena_allocated_impl_for_stream!(StandardErrorStream, StandardErrorStream);

#[derive(Debug, Copy, Clone)]
pub enum Stream {
    Byte(TypedArenaPtr<StreamLayout<CharReader<ByteStream>>>),
    InputFile(TypedArenaPtr<StreamLayout<CharReader<InputFileStream>>>),
    OutputFile(TypedArenaPtr<StreamLayout<OutputFileStream>>),
    StaticString(TypedArenaPtr<StreamLayout<StaticStringStream>>),
    NamedTcp(TypedArenaPtr<StreamLayout<CharReader<NamedTcpStream>>>),
    NamedTls(TypedArenaPtr<StreamLayout<CharReader<NamedTlsStream>>>),
    HttpRead(TypedArenaPtr<StreamLayout<CharReader<HttpReadStream>>>),
    HttpWrite(TypedArenaPtr<StreamLayout<CharReader<HttpWriteStream>>>),
    Null(StreamOptions),
    Readline(TypedArenaPtr<StreamLayout<ReadlineStream>>),
    StandardOutput(TypedArenaPtr<StreamLayout<StandardOutputStream>>),
    StandardError(TypedArenaPtr<StreamLayout<StandardErrorStream>>),
}

impl From<TypedArenaPtr<StreamLayout<ReadlineStream>>> for Stream {
    #[inline]
    fn from(stream: TypedArenaPtr<StreamLayout<ReadlineStream>>) -> Stream {
        Stream::Readline(stream)
    }
}

impl Stream {
    #[inline]
    pub fn from_readline_stream(stream: ReadlineStream, arena: &mut Arena) -> Stream {
        Stream::Readline(arena_alloc!(StreamLayout::new(stream), arena))
    }

    #[inline]
    pub fn from_owned_string(string: String, arena: &mut Arena) -> Stream {
        Stream::Byte(arena_alloc!(
            StreamLayout::new(CharReader::new(ByteStream(Cursor::new(string.into_bytes())))),
            arena
        ))
    }

    #[inline]
    pub fn from_static_string(src: &'static str, arena: &mut Arena) -> Stream {
        Stream::StaticString(arena_alloc!(
            StreamLayout::new(StaticStringStream {
                stream: Cursor::new(src)
            }),
            arena
        ))
    }

    #[inline]
    pub fn stdin(arena: &mut Arena, add_history: bool) -> Stream {
        Stream::Readline(arena_alloc!(
            StreamLayout::new(ReadlineStream::new("", add_history)),
            arena
        ))
    }

    pub fn from_tag(tag: ArenaHeaderTag, ptr: *const u8) -> Self {
        match tag {
            ArenaHeaderTag::ByteStream => Stream::Byte(TypedArenaPtr::new(ptr as *mut _)),
            ArenaHeaderTag::InputFileStream => Stream::InputFile(TypedArenaPtr::new(ptr as *mut _)),
            ArenaHeaderTag::OutputFileStream => {
                Stream::OutputFile(TypedArenaPtr::new(ptr as *mut _))
            }
            ArenaHeaderTag::NamedTcpStream => Stream::NamedTcp(TypedArenaPtr::new(ptr as *mut _)),
            ArenaHeaderTag::NamedTlsStream => Stream::NamedTls(TypedArenaPtr::new(ptr as *mut _)),
            ArenaHeaderTag::HttpReadStream => Stream::HttpRead(TypedArenaPtr::new(ptr as *mut _)),
	    ArenaHeaderTag::HttpWriteStream => Stream::HttpWrite(TypedArenaPtr::new(ptr as *mut _)),
            ArenaHeaderTag::ReadlineStream => Stream::Readline(TypedArenaPtr::new(ptr as *mut _)),
            ArenaHeaderTag::StaticStringStream => {
                Stream::StaticString(TypedArenaPtr::new(ptr as *mut _))
            }
            ArenaHeaderTag::StandardOutputStream => {
                Stream::StandardOutput(TypedArenaPtr::new(ptr as *mut _))
            }
            ArenaHeaderTag::StandardErrorStream => {
                Stream::StandardError(TypedArenaPtr::new(ptr as *mut _))
            }
            ArenaHeaderTag::Dropped | ArenaHeaderTag::NullStream => {
                Stream::Null(StreamOptions::default())
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn is_stderr(&self) -> bool {
        if let Stream::StandardError(_) = self {
            true
        } else {
            false
        }
    }

    #[inline]
    pub fn is_stdout(&self) -> bool {
        if let Stream::StandardOutput(_) = self {
            true
        } else {
            false
        }
    }

    #[inline]
    pub fn is_stdin(&self) -> bool {
        if let Stream::Readline(_) = self {
            true
        } else {
            false
        }
    }

    pub fn as_ptr(&self) -> *const ArenaHeader {
        match self {
            Stream::Byte(ptr) => ptr.header_ptr(),
            Stream::InputFile(ptr) => ptr.header_ptr(),
            Stream::OutputFile(ptr) => ptr.header_ptr(),
            Stream::StaticString(ptr) => ptr.header_ptr(),
            Stream::NamedTcp(ptr) => ptr.header_ptr(),
            Stream::NamedTls(ptr) => ptr.header_ptr(),
            Stream::HttpRead(ptr) => ptr.header_ptr(),
	    Stream::HttpWrite(ptr) => ptr.header_ptr(),
            Stream::Null(_) => ptr::null(),
            Stream::Readline(ptr) => ptr.header_ptr(),
            Stream::StandardOutput(ptr) => ptr.header_ptr(),
            Stream::StandardError(ptr) => ptr.header_ptr(),
        }
    }

    pub fn options(&self) -> &StreamOptions {
        match self {
            Stream::Byte(ref ptr) => &ptr.options,
            Stream::InputFile(ref ptr) => &ptr.options,
            Stream::OutputFile(ref ptr) => &ptr.options,
            Stream::StaticString(ref ptr) => &ptr.options,
            Stream::NamedTcp(ref ptr) => &ptr.options,
            Stream::NamedTls(ref ptr) => &ptr.options,
            Stream::HttpRead(ref ptr) => &ptr.options,
	    Stream::HttpWrite(ref ptr) => &ptr.options,
            Stream::Null(ref options) => options,
            Stream::Readline(ref ptr) => &ptr.options,
            Stream::StandardOutput(ref ptr) => &ptr.options,
            Stream::StandardError(ref ptr) => &ptr.options,
        }
    }

    pub fn options_mut(&mut self) -> &mut StreamOptions {
        match self {
            Stream::Byte(ref mut ptr) => &mut ptr.options,
            Stream::InputFile(ref mut ptr) => &mut ptr.options,
            Stream::OutputFile(ref mut ptr) => &mut ptr.options,
            Stream::StaticString(ref mut ptr) => &mut ptr.options,
            Stream::NamedTcp(ref mut ptr) => &mut ptr.options,
            Stream::NamedTls(ref mut ptr) => &mut ptr.options,
            Stream::HttpRead(ref mut ptr) => &mut ptr.options,
            Stream::HttpWrite(ref mut ptr) => &mut ptr.options,	    
            Stream::Null(ref mut options) => options,
            Stream::Readline(ref mut ptr) => &mut ptr.options,
            Stream::StandardOutput(ref mut ptr) => &mut ptr.options,
            Stream::StandardError(ref mut ptr) => &mut ptr.options,
        }
    }

    #[inline]
    pub(crate) fn add_lines_read(&mut self, incr_num_lines_read: usize) {
        match self {
            Stream::Byte(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::InputFile(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::OutputFile(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::StaticString(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::NamedTcp(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::NamedTls(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::HttpRead(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::HttpWrite(_) => {}	 
            Stream::Null(_) => {}
            Stream::Readline(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::StandardOutput(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::StandardError(ptr) => ptr.lines_read += incr_num_lines_read,
        }
    }

    #[inline]
    pub(crate) fn set_lines_read(&mut self, value: usize) {
        match self {
            Stream::Byte(ptr) => ptr.lines_read = value,
            Stream::InputFile(ptr) => ptr.lines_read = value,
            Stream::OutputFile(ptr) => ptr.lines_read = value,
            Stream::StaticString(ptr) => ptr.lines_read = value,
            Stream::NamedTcp(ptr) => ptr.lines_read = value,
            Stream::NamedTls(ptr) => ptr.lines_read = value,
            Stream::HttpRead(ptr) => ptr.lines_read = value,
            Stream::HttpWrite(_) => {}	    
            Stream::Null(_) => {}
            Stream::Readline(ptr) => ptr.lines_read = value,
            Stream::StandardOutput(ptr) => ptr.lines_read = value,
            Stream::StandardError(ptr) => ptr.lines_read = value,
        }
    }

    #[inline]
    pub(crate) fn lines_read(&self) -> usize {
        match self {
            Stream::Byte(ptr) => ptr.lines_read,
            Stream::InputFile(ptr) => ptr.lines_read,
            Stream::OutputFile(ptr) => ptr.lines_read,
            Stream::StaticString(ptr) => ptr.lines_read,
            Stream::NamedTcp(ptr) => ptr.lines_read,
            Stream::NamedTls(ptr) => ptr.lines_read,
            Stream::HttpRead(ptr) => ptr.lines_read,
            Stream::HttpWrite(_) => 0,	  
            Stream::Null(_) => 0,
            Stream::Readline(ptr) => ptr.lines_read,
            Stream::StandardOutput(ptr) => ptr.lines_read,
            Stream::StandardError(ptr) => ptr.lines_read,
        }
    }
}

impl CharRead for Stream {
    fn peek_char(&mut self) -> Option<std::io::Result<char>> {
        match self {
            Stream::InputFile(file) => (*file).peek_char(),
            Stream::NamedTcp(tcp_stream) => (*tcp_stream).peek_char(),
            Stream::NamedTls(tls_stream) => (*tls_stream).peek_char(),
            Stream::HttpRead(http_stream) => (*http_stream).peek_char(),
            Stream::Readline(rl_stream) => (*rl_stream).peek_char(),
            Stream::StaticString(src) => (*src).peek_char(),
            Stream::Byte(cursor) => (*cursor).peek_char(),
            Stream::OutputFile(_) |
            Stream::StandardError(_) |
            Stream::StandardOutput(_) |
	    Stream::HttpWrite(_) |
            Stream::Null(_) => Some(Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            ))),
        }
    }

    fn read_char(&mut self) -> Option<std::io::Result<char>> {
        match self {
            Stream::InputFile(file) => (*file).read_char(),
            Stream::NamedTcp(tcp_stream) => (*tcp_stream).read_char(),
            Stream::NamedTls(tls_stream) => (*tls_stream).read_char(),
            Stream::HttpRead(http_stream) => (*http_stream).read_char(),
            Stream::Readline(rl_stream) => (*rl_stream).read_char(),
            Stream::StaticString(src) => (*src).read_char(),
            Stream::Byte(cursor) => (*cursor).read_char(),
            Stream::OutputFile(_) |
            Stream::StandardError(_) |
            Stream::StandardOutput(_) |
	    Stream::HttpWrite(_) |
            Stream::Null(_) => Some(Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            ))),
        }
    }

    fn put_back_char(&mut self, c: char) {
        match self {
            Stream::InputFile(file) => file.put_back_char(c),
            Stream::NamedTcp(tcp_stream) => tcp_stream.put_back_char(c),
            Stream::NamedTls(tls_stream) => tls_stream.put_back_char(c),
            Stream::HttpRead(http_stream) => http_stream.put_back_char(c),
            Stream::Readline(rl_stream) => rl_stream.put_back_char(c),
            Stream::StaticString(src) => src.put_back_char(c),
            Stream::Byte(cursor) => cursor.put_back_char(c),
            Stream::OutputFile(_) |
            Stream::StandardError(_) |
            Stream::StandardOutput(_) |
	    Stream::HttpWrite(_) |
            Stream::Null(_) => {}
        }
    }

    fn consume(&mut self, nread: usize) {
        match self {
            Stream::InputFile(ref mut file) => file.consume(nread),
            Stream::NamedTcp(ref mut tcp_stream) => tcp_stream.consume(nread),
            Stream::NamedTls(ref mut tls_stream) => tls_stream.consume(nread),
            Stream::HttpRead(ref mut http_stream) => http_stream.consume(nread),
            Stream::Readline(ref mut rl_stream) => rl_stream.consume(nread),
            Stream::StaticString(ref mut src) => src.consume(nread),
            Stream::Byte(ref mut cursor) => cursor.consume(nread),
            Stream::OutputFile(_) |
            Stream::StandardError(_) |
            Stream::StandardOutput(_) |
	    Stream::HttpWrite(_) |
            Stream::Null(_) => {}
        }
    }
}

impl Read for Stream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let bytes_read = match self {
            Stream::InputFile(file) => (*file).read(buf),
            Stream::NamedTcp(tcp_stream) => (*tcp_stream).read(buf),
            Stream::NamedTls(tls_stream) => (*tls_stream).read(buf),
            Stream::HttpRead(http_stream) => (*http_stream).read(buf),
            Stream::Readline(rl_stream) => (*rl_stream).read(buf),
            Stream::StaticString(src) => (*src).read(buf),
            Stream::Byte(cursor) => (*cursor).read(buf),
            Stream::OutputFile(_)
            | Stream::StandardError(_)
	    | Stream::StandardOutput(_)
	    | Stream::HttpWrite(_)
            | Stream::Null(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            )),
        };

        bytes_read
    }
}

impl Write for Stream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Stream::OutputFile(ref mut file) => file.write(buf),
            Stream::NamedTcp(ref mut tcp_stream) => tcp_stream.get_mut().write(buf),
            Stream::NamedTls(ref mut tls_stream) => tls_stream.get_mut().write(buf),
            Stream::Byte(ref mut cursor) => cursor.get_mut().write(buf),
            Stream::StandardOutput(stream) => stream.write(buf),
            Stream::StandardError(stream) => stream.write(buf),
	    Stream::HttpWrite(ref mut stream) => stream.get_mut().write(buf),
            Stream::HttpRead(_) |
            Stream::StaticString(_) |
            Stream::Readline(_) |
            Stream::InputFile(..) |
            Stream::Null(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::WriteToInputStream,
            )),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Stream::OutputFile(ref mut file) => file.stream.flush(),
            Stream::NamedTcp(ref mut tcp_stream) => tcp_stream.stream.get_mut().flush(),
            Stream::NamedTls(ref mut tls_stream) => tls_stream.stream.get_mut().flush(),
            Stream::Byte(ref mut cursor) => cursor.stream.get_mut().flush(),
            Stream::StandardError(stream) => stream.stream.flush(),
            Stream::StandardOutput(stream) => stream.stream.flush(),
	    Stream::HttpWrite(ref mut stream) => stream.stream.get_mut().flush(),
            Stream::HttpRead(_) |
            Stream::StaticString(_) |
            Stream::Readline(_) |
            Stream::InputFile(_) |
            Stream::Null(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::FlushToInputStream,
            )),
        }
    }
}

#[derive(Debug)]
enum StreamError {
    PeekByteFailed,
    PeekByteFromNonPeekableStream,
    #[allow(unused)] PeekCharFailed,
    #[allow(unused)] PeekCharFromNonPeekableStream,
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
        self.as_ptr() == other.as_ptr()
    }
}

impl Eq for Stream {}

impl Stream {
    #[inline]
    pub(crate) fn position(&mut self) -> Option<(u64, usize)> {
        // returns lines_read, position.
        let result = match self {
            Stream::InputFile(file_stream) => {
                file_stream.position()
            }
            Stream::NamedTcp(..)
            | Stream::NamedTls(..)
            | Stream::Readline(..)
            | Stream::StaticString(..)
            | Stream::Byte(..) => Some(0),
            _ => None,
        };

        result.map(|position| (position, self.lines_read()))
    }

    #[inline]
    pub(crate) fn set_position(&mut self, position: u64) {
        match self {
            Stream::InputFile(stream_layout) => {
                let StreamLayout {
                    past_end_of_stream,
                    stream,
                    ..
                } = &mut **stream_layout;

                stream.get_mut().file.seek(SeekFrom::Start(position)).unwrap();
                stream.reset_buffer(); // flush the internal buffer.

                if let Ok(metadata) = stream.get_ref().file.metadata() {
                    *past_end_of_stream = position > metadata.len();
                }
            }
            _ => {}
        }
    }

    #[inline]
    pub(crate) fn past_end_of_stream(&self) -> bool {
        match self {
            Stream::Byte(stream) => stream.past_end_of_stream,
            Stream::InputFile(stream) => stream.past_end_of_stream,
            Stream::OutputFile(stream) => stream.past_end_of_stream,
            Stream::StaticString(stream) => stream.past_end_of_stream,
            Stream::NamedTcp(stream) => stream.past_end_of_stream,
            Stream::NamedTls(stream) => stream.past_end_of_stream,
            Stream::HttpRead(stream) => stream.past_end_of_stream,
            Stream::HttpWrite(stream) => stream.past_end_of_stream,	    
            Stream::Null(_) => false,
            Stream::Readline(stream) => stream.past_end_of_stream,
            Stream::StandardOutput(stream) => stream.past_end_of_stream,
            Stream::StandardError(stream) => stream.past_end_of_stream,
        }
    }

    #[inline]
    pub(crate) fn at_end_of_stream(&mut self) -> bool {
        self.position_relative_to_end() == AtEndOfStream::At
    }

    #[inline]
    pub(crate) fn set_past_end_of_stream(&mut self, value: bool) {
        match self {
            Stream::Byte(stream) => stream.past_end_of_stream = value,
            Stream::InputFile(stream) => stream.past_end_of_stream = value,
            Stream::OutputFile(stream) => stream.past_end_of_stream = value,
            Stream::StaticString(stream) => stream.past_end_of_stream = value,
            Stream::NamedTcp(stream) => stream.past_end_of_stream = value,
            Stream::NamedTls(stream) => stream.past_end_of_stream = value,
            Stream::HttpRead(stream) => stream.past_end_of_stream = value,
            Stream::HttpWrite(stream) => stream.past_end_of_stream = value,	    
            Stream::Null(_) => {}
            Stream::Readline(stream) => stream.past_end_of_stream = value,
            Stream::StandardOutput(stream) => stream.past_end_of_stream = value,
            Stream::StandardError(stream) => stream.past_end_of_stream = value,
        }
    }

    #[inline]
    pub(crate) fn position_relative_to_end(&mut self) -> AtEndOfStream {
        if self.past_end_of_stream() {
            return AtEndOfStream::Past;
        }

        if let Stream::InputFile(stream_layout) = self {
            let position = stream_layout.position();

            let StreamLayout {
                past_end_of_stream,
                stream,
                ..
            } = &mut **stream_layout;

            match stream.get_ref().file.metadata() {
                Ok(metadata) => {
                    if let Some(position) = position {
                        return match position.cmp(&metadata.len()) {
                            Ordering::Equal => AtEndOfStream::At,
                            Ordering::Less => AtEndOfStream::Not,
                            Ordering::Greater => {
                                *past_end_of_stream = true;
                                AtEndOfStream::Past
                            }
                        };
                    } else {
                        *past_end_of_stream = true;
                        AtEndOfStream::Past
                    }
                }
                _ => {
                    *past_end_of_stream = true;
                    AtEndOfStream::Past
                }
            }
        } else {
            AtEndOfStream::Not
        }
    }

    #[inline]
    pub(crate) fn file_name(&self) -> Option<Atom> {
        match self {
            Stream::InputFile(file) => Some(file.stream.get_ref().file_name),
            Stream::OutputFile(file) => Some(file.stream.file_name),
            Stream::NamedTcp(tcp) => Some(tcp.stream.get_ref().address),
            Stream::NamedTls(tls) => Some(tls.stream.get_ref().address),
            _ => None,
        }
    }

    #[inline]
    pub(crate) fn mode(&self) -> Atom {
        match self {
            Stream::Byte(_)
            | Stream::Readline(_)
            | Stream::StaticString(_)
            | Stream::HttpRead(_)
            | Stream::InputFile(..) => atom!("read"),
            Stream::NamedTcp(..) | Stream::NamedTls(..) => atom!("read_append"),
            Stream::OutputFile(file) if file.is_append => atom!("append"),
            Stream::OutputFile(_) | Stream::StandardError(_) | Stream::StandardOutput(_) | Stream::HttpWrite(_) => atom!("write"),
            Stream::Null(_) => atom!(""),
        }
    }

    #[inline]
    pub fn stdout(arena: &mut Arena) -> Self {
        Stream::StandardOutput(arena_alloc!(
            StreamLayout::new(StandardOutputStream {}),
            arena
        ))
    }

    #[inline]
    pub fn stderr(arena: &mut Arena) -> Self {
        Stream::StandardError(arena_alloc!(
            StreamLayout::new(StandardErrorStream {}),
            arena
        ))
    }

    #[inline]
    pub(crate) fn from_tcp_stream(
        address: Atom,
        tcp_stream: TcpStream,
        arena: &mut Arena,
    ) -> Self {
        tcp_stream.set_read_timeout(None).unwrap();
        tcp_stream.set_write_timeout(None).unwrap();

        Stream::NamedTcp(arena_alloc!(
            StreamLayout::new(CharReader::new(NamedTcpStream {
                address,
                tcp_stream
            })),
            arena
        ))
    }

    #[inline]
    pub(crate) fn from_tls_stream(
        address: Atom,
        tls_stream: TlsStream<Stream>,
        arena: &mut Arena,
    ) -> Self {
        Stream::NamedTls(arena_alloc!(
            StreamLayout::new(CharReader::new(NamedTlsStream {
                address,
                tls_stream
            })),
            arena
        ))
    }

    #[inline]
    pub(crate) fn from_http_stream(
        url: Atom,
        http_stream: Box<dyn BufRead>,
        arena: &mut Arena,
    ) -> Self {
        Stream::HttpRead(arena_alloc!(
            StreamLayout::new(CharReader::new(HttpReadStream {
                url,
                body_reader: http_stream
            })),
            arena
        ))
    }

    #[inline]
    pub(crate) fn from_http_sender(
	body_writer: Sender,
	arena: &mut Arena,
    ) -> Self {
	Stream::HttpWrite(arena_alloc!(
	    StreamLayout::new(CharReader::new(HttpWriteStream {
		body_writer
	    })),
	    arena
	))
    }

    #[inline]
    pub(crate) fn from_file_as_output(
        file_name: Atom,
        file: File,
        is_append: bool,
        arena: &mut Arena,
    ) -> Self {
        Stream::OutputFile(arena_alloc!(
            StreamLayout::new(OutputFileStream {
                file_name,
                file,
                is_append
            }),
            arena
        ))
    }

    #[inline]
    pub(crate) fn from_file_as_input(file_name: Atom, file: File, arena: &mut Arena) -> Self {
        Stream::InputFile(arena_alloc!(
            StreamLayout::new(CharReader::new(InputFileStream { file_name, file })),
            arena
        ))
    }

    #[inline]
    pub(crate) fn close(&mut self) -> Result<(), std::io::Error> {
        let mut stream = std::mem::replace(self, Stream::Null(StreamOptions::default()));

        match stream {
            Stream::NamedTcp(ref mut tcp_stream) => {
                tcp_stream.inner_mut().tcp_stream.shutdown(Shutdown::Both)
            },
            Stream::NamedTls(ref mut tls_stream) => {
                tls_stream.inner_mut().tls_stream.shutdown()
            }
            Stream::HttpRead(ref mut http_stream) => {
                unsafe {
                    http_stream.set_tag(ArenaHeaderTag::Dropped);
                    std::ptr::drop_in_place(&mut http_stream.inner_mut().body_reader as *mut _);
                }

                Ok(())
            }
	        Stream::HttpWrite(ref mut http_stream) => {
                unsafe {
                    http_stream.set_tag(ArenaHeaderTag::Dropped);
                    std::ptr::drop_in_place(&mut http_stream.inner_mut().body_writer as *mut _);
                }

                Ok(())
	        }
            Stream::InputFile(mut file_stream) => {
                // close the stream by dropping the inner File.
                unsafe {
                    file_stream.set_tag(ArenaHeaderTag::Dropped);
                    std::ptr::drop_in_place(&mut file_stream.inner_mut().file as *mut _);
                }

                Ok(())
            }
            Stream::OutputFile(mut file_stream) => {
                // close the stream by dropping the inner File.
                unsafe {
                    file_stream.set_tag(ArenaHeaderTag::Dropped);
                    std::ptr::drop_in_place(&mut file_stream.file as *mut _);
                }

                Ok(())
            }
            _ => Ok(())
        }
    }

    #[inline]
    pub(crate) fn is_null_stream(&self) -> bool {
        if let Stream::Null(_) = self {
            true
        } else {
            false
        }
    }

    #[inline]
    pub(crate) fn is_input_stream(&self) -> bool {
        match self {
            Stream::NamedTcp(..)
            | Stream::NamedTls(..)
            | Stream::HttpRead(..)
            | Stream::Byte(_)
            | Stream::Readline(_)
            | Stream::StaticString(_)
            | Stream::InputFile(..) => true,
            _ => false,
        }
    }

    #[inline]
    pub(crate) fn is_output_stream(&self) -> bool {
        match self {
            Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::NamedTcp(..)
	    | Stream::NamedTls(..)
	    | Stream::HttpWrite(..)	
            | Stream::Byte(_)
            | Stream::OutputFile(..) => true,
            _ => false,
        }
    }

    // returns true on success.
    #[inline]
    pub(super) fn reset(&mut self) -> bool {
        self.set_lines_read(0);
        self.set_past_end_of_stream(false);

        loop {
            match self {
                Stream::Byte(ref mut cursor) => {
                    cursor.stream.get_mut().0.set_position(0);
                    return true;
                }
                Stream::InputFile(ref mut file_stream) => {
                    file_stream.stream.get_mut().file.seek(SeekFrom::Start(0)).unwrap();
                    return true;
                }
                Stream::Readline(ref mut readline_stream) => {
                    readline_stream.reset();
                    return true;
                }
                _ => {
                    return false;
                }
            }
        }
    }

    #[inline]
    pub(crate) fn peek_byte(&mut self) -> std::io::Result<u8> {
        match self {
            Stream::Byte(ref mut cursor) => {
                let mut b = [0u8; 1];
                let pos = cursor.stream.get_mut().0.position();

                match cursor.read(&mut b)? {
                    1 => {
                        cursor.stream.get_mut().0.set_position(pos);
                        Ok(b[0])
                    }
                    _ => Err(std::io::Error::new(ErrorKind::UnexpectedEof, "end of file")),
                }
            }
            Stream::InputFile(ref mut file) => {
                let mut b = [0u8; 1];

                match file.read(&mut b)? {
                    1 => {
                        file.stream.get_mut().file.seek(SeekFrom::Current(-1))?;
                        Ok(b[0])
                    }
                    _ => Err(std::io::Error::new(
                        ErrorKind::UnexpectedEof,
                        StreamError::PeekByteFailed,
                    )),
                }
            }
            Stream::Readline(ref mut stream) => stream.stream.peek_byte(),
            Stream::NamedTcp(ref mut stream) => {
                let mut b = [0u8; 1];
                stream.stream.get_mut().tcp_stream.peek(&mut b)?;
                Ok(b[0])
            }
            _ => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::PeekByteFromNonPeekableStream,
            )),
        }
    }
}

impl MachineState {
    #[inline]
    pub(crate) fn eof_action(
        &mut self,
        result: HeapCellValue,
        mut stream: Stream,
        caller: Atom,
        arity: usize,
    ) -> CallResult {
        let eof_action = stream.options().eof_action();

        match eof_action {
            EOFAction::Error => {
                stream.set_past_end_of_stream(true);
                return Err(self.open_past_eos_error(stream, caller, arity));
            }
            EOFAction::EOFCode => {
                let end_of_stream = if stream.options().stream_type() == StreamType::Binary {
                    fixnum_as_cell!(Fixnum::build_with(-1))
                } else {
                    atom_as_cell!(atom!("end_of_file"))
                };

                stream.set_past_end_of_stream(true);
                Ok(unify!(self, result, end_of_stream))
            }
            EOFAction::Reset => {
                if !stream.reset() {
                    stream.set_past_end_of_stream(true);
                }

                Ok(self.fail = stream.past_end_of_stream())
            }
        }
    }

    pub(crate) fn to_stream_options(
        &mut self,
        alias: HeapCellValue,
        eof_action: HeapCellValue,
        reposition: HeapCellValue,
        stream_type: HeapCellValue,
    ) -> StreamOptions {
        let alias = read_heap_cell!(self.store(MachineState::deref(self, alias)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                if name != atom!("[]") {
                    Some(name)
                } else {
                    None
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);

                if name != atom!("[]") {
                    Some(name)
                } else {
                    None
                }
            }
            _ => {
                None
            }
        );

        let eof_action = read_heap_cell!(self.store(MachineState::deref(self, eof_action)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                match name  {
                    atom!("eof_code") => EOFAction::EOFCode,
                    atom!("error") => EOFAction::Error,
                    atom!("reset") => EOFAction::Reset,
                    _ => unreachable!(),
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);

                match name  {
                    atom!("eof_code") => EOFAction::EOFCode,
                    atom!("error") => EOFAction::Error,
                    atom!("reset") => EOFAction::Reset,
                    _ => unreachable!(),
                }
            }
            _ => {
                unreachable!()
            }
        );

        let reposition = read_heap_cell!(self.store(MachineState::deref(self, reposition)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                name == atom!("true")
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                name == atom!("true")
            }
            _ => {
                unreachable!()
            }
        );

        let stream_type = read_heap_cell!(self.store(MachineState::deref(self, stream_type)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                match name {
                    atom!("text") => StreamType::Text,
                    atom!("binary") => StreamType::Binary,
                    _ => unreachable!(),
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                match name {
                    atom!("text") => StreamType::Text,
                    atom!("binary") => StreamType::Binary,
                    _ => unreachable!(),
                }
            }
            _ => {
                unreachable!()
            }
        );

        let mut options = StreamOptions::default();

        options.set_stream_type(stream_type);
        options.set_reposition(reposition);
        options.set_alias_to_atom_opt(alias);
        options.set_eof_action(eof_action);

        options
    }

    pub(crate) fn get_stream_or_alias(
        &mut self,
        addr: HeapCellValue,
        stream_aliases: &StreamAliasDir,
        caller: Atom,
        arity: usize,
    ) -> Result<Stream, MachineStub> {
        let addr = self.store(MachineState::deref(self, addr));

        read_heap_cell!(addr,
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                return match stream_aliases.get(&name) {
                    Some(stream) if !stream.is_null_stream() => Ok(*stream),
                    _ => {
                        let stub = functor_stub(caller, arity);
                        let addr = atom_as_cell!(name);

                        let existence_error = self.existence_error(ExistenceError::Stream(addr));

                        Err(self.error_form(existence_error, stub))
                    }
                };
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);

                return match stream_aliases.get(&name) {
                    Some(stream) if !stream.is_null_stream() => Ok(*stream),
                    _ => {
                        let stub = functor_stub(caller, arity);
                        let addr = atom_as_cell!(name);

                        let existence_error = self.existence_error(ExistenceError::Stream(addr));

                        Err(self.error_form(existence_error, stub))
                    }
                };
            }
            (HeapCellValueTag::Cons, ptr) => {
                match_untyped_arena_ptr!(ptr,
                     (ArenaHeaderTag::Stream, stream) => {
                         return if stream.is_null_stream() {
                             Err(self.open_permission_error(stream_as_cell!(stream), caller, arity))
                         } else {
                             Ok(stream)
                         };
                     }
                     (ArenaHeaderTag::Dropped, _value) => {
                         let stub = functor_stub(caller, arity);
                         let err = self.existence_error(ExistenceError::Stream(addr));

                         return Err(self.error_form(err, stub));
                     }
                     _ => {
                     }
                );
            }
            _ => {
            }
        );

        let stub = functor_stub(caller, arity);

        if addr.is_var() {
            let instantiation_error = self.instantiation_error();
            Err(self.error_form(instantiation_error, stub))
        } else {
            let domain_error = self.domain_error(DomainErrorType::StreamOrAlias, addr);
            Err(self.error_form(domain_error, stub))
        }
    }

    pub(crate) fn open_parsing_stream(
        &mut self,
        mut stream: Stream,
        stub_name: Atom,
        stub_arity: usize,
    ) -> Result<Stream, MachineStub> {
        match stream.peek_char() {
            None => Ok(stream), // empty stream is handled gracefully by Lexer::eof
            Some(Err(e)) => {
                let err = self.session_error(SessionError::from(e));
                let stub = functor_stub(stub_name, stub_arity);

                Err(self.error_form(err, stub))
            }
            Some(Ok(c)) => {
                if c == '\u{feff}' {
                    // skip UTF-8 BOM
                    stream.consume(c.len_utf8());
                }

                Ok(stream)
            }
        }
    }

    pub(crate) fn stream_permission_error(
        &mut self,
        perm: Permission,
        err_atom: Atom,
        stream: Stream,
        caller: Atom,
        arity: usize,
    ) -> MachineStub {
        let stub = functor_stub(caller, arity);
        let err  = self.permission_error(perm, err_atom, stream_as_cell!(stream));

        self.error_form(err, stub)
    }

    #[inline]
    pub(crate) fn open_past_eos_error(
        &mut self,
        stream: Stream,
        caller: Atom,
        arity: usize,
    ) -> MachineStub {
        self.stream_permission_error(
            Permission::InputStream,
            atom!("past_end_of_stream"),
            stream,
            caller,
            arity,
        )
    }

    pub(crate) fn open_permission_error<T: PermissionError>(
        &mut self,
        culprit: T,
        stub_name: Atom,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);
        let err  = self.permission_error(Permission::Open, atom!("source_sink"), culprit);

        self.error_form(err, stub)
    }

    pub(crate) fn occupied_alias_permission_error(
        &mut self,
        alias: Atom,
        stub_name: Atom,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);

        let err = self.permission_error(
            Permission::Open,
            atom!("source_sink"),
            functor!(atom!("alias"), [atom(alias)]),
        );

        self.error_form(err, stub)
    }

    pub(crate) fn reposition_error(&mut self, stub_name: Atom, stub_arity: usize) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);
        let rep_stub = functor!(atom!("reposition"), [atom(atom!("true"))]);
        let err = self.permission_error(Permission::Open, atom!("source_sink"), rep_stub);

        self.error_form(err, stub)
    }

    pub(crate) fn check_stream_properties(
        &mut self,
        stream: Stream,
        expected_type: StreamType,
        input: Option<HeapCellValue>,
        caller: Atom,
        arity: usize,
    ) -> CallResult {
        let opt_err = if input.is_some() && !stream.is_input_stream() {
            Some(atom!("stream")) // 8.14.2.3 g)
        } else if input.is_none() && !stream.is_output_stream() {
            Some(atom!("stream")) // 8.14.2.3 g)
        } else if stream.options().stream_type() != expected_type {
            Some(expected_type.other().as_atom()) // 8.14.2.3 h)
        } else {
            None
        };

        let permission = if input.is_some() {
            Permission::InputStream
        } else {
            Permission::OutputStream
        };

        if let Some(err_atom) = opt_err {
            return Err(self.stream_permission_error(permission, err_atom, stream, caller, arity));
        }

        if let Some(input) = input {
            if stream.past_end_of_stream() {
                self.eof_action(input, stream, caller, arity)?;
            }
        }

        Ok(())
    }

    pub(crate) fn stream_from_file_spec(
        &mut self,
        file_spec: Atom,
        indices: &mut IndexStore,
        options: &StreamOptions,
    ) -> Result<Stream, MachineStub> {
        if file_spec == atom!("") {
            let stub = functor_stub(atom!("open"), 4);
            let err = self.domain_error(DomainErrorType::SourceSink, self[temp_v!(1)]);

            return Err(self.error_form(err, stub));
        }

        // 8.11.5.3l)
        if let Some(alias) = options.get_alias() {
            if indices.stream_aliases.contains_key(&alias) {
                return Err(self.occupied_alias_permission_error(alias, atom!("open"), 4));
            }
        }

        let mode = MachineState::deref(self, self[temp_v!(2)]);
        let mode = cell_as_atom!(self.store(mode));

        let mut open_options = OpenOptions::new();

        let (is_input_file, in_append_mode) = match mode {
            atom!("read") => {
                open_options.read(true).write(false).create(false);
                (true, false)
            }
            atom!("write") => {
                open_options
                    .read(false)
                    .write(true)
                    .truncate(true)
                    .create(true);

                (false, false)
            }
            atom!("append") => {
                open_options
                    .read(false)
                    .write(true)
                    .create(true)
                    .append(true);

                (false, true)
            }
            _ => {
                let stub = functor_stub(atom!("open"), 4);
                let err = self.domain_error(DomainErrorType::IOMode, self[temp_v!(2)]);

                // 8.11.5.3h)
                return Err(self.error_form(err, stub));
            }
        };

        let file = match open_options.open(file_spec.as_str()) {
            Ok(file) => file,
            Err(err) => {
                match err.kind() {
                    ErrorKind::NotFound => {
                        // 8.11.5.3j)
                        let stub = functor_stub(atom!("open"), 4);

                        let err = self.existence_error(
                            ExistenceError::SourceSink(self[temp_v!(1)]),
                        );

                        return Err(self.error_form(err, stub));
                    }
                    ErrorKind::PermissionDenied => {
                        // 8.11.5.3k)
                        return Err(self.open_permission_error(self[temp_v!(1)], atom!("open"), 4));
                    }
                    _ => {
                        let stub = functor_stub(atom!("open"), 4);
                        let err = self.syntax_error(ParserError::IO(err));

                        return Err(self.error_form(err, stub));
                    }
                }
            }
        };

        Ok(if is_input_file {
            Stream::from_file_as_input(file_spec, file, &mut self.arena)
        } else {
            Stream::from_file_as_output(file_spec, file, in_append_mode, &mut self.arena)
        })
    }
}
