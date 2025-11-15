use crate::arena::*;
use crate::atom_table::*;
use crate::functor_macro::*;
use crate::parser::ast::*;
use crate::parser::char_reader::*;
use crate::read::*;

#[cfg(feature = "http")]
use crate::http::HttpResponse;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::types::*;

pub use scryer_modular_bitfield::prelude::*;

#[cfg(feature = "http")]
use bytes::{buf::Reader as BufReader, Buf, Bytes};
use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::fmt::Debug;
use std::fs::{File, OpenOptions};
use std::hash::Hash;
use std::io;
use std::io::{Cursor, ErrorKind, Read, Seek, SeekFrom, Write};
use std::mem::ManuallyDrop;
use std::net::{Shutdown, TcpStream};
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::ptr;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::TryRecvError;

#[cfg(feature = "tls")]
use native_tls::TlsStream;

#[cfg(feature = "http")]
use warp::hyper;

mod compat;
pub use compat::*;

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
        self.get_mut()
            .file
            .stream_position()
            .map(|pos| pos - self.stream.rem_buf_len() as u64)
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
        self.stream.get_ref()[pos..].chars().next().map(Ok)
    }

    #[inline(always)]
    fn consume(&mut self, nread: usize) {
        self.stream.seek(SeekFrom::Current(nread as i64)).unwrap();
    }

    #[inline(always)]
    fn put_back_char(&mut self, c: char) {
        self.stream
            .seek(SeekFrom::Current(-(c.len_utf8() as i64)))
            .unwrap();
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

#[cfg(feature = "tls")]
#[derive(Debug)]
pub struct NamedTlsStream {
    address: Atom,
    tls_stream: TlsStream<Stream>,
}

#[cfg(feature = "tls")]
impl Read for NamedTlsStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.tls_stream.read(buf)
    }
}

#[cfg(feature = "tls")]
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

#[cfg(feature = "http")]
pub struct HttpReadStream {
    url: Atom,
    body_reader: BufReader<Bytes>,
}

#[cfg(feature = "http")]
impl Debug for HttpReadStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Http Read Stream [{}]", self.url.as_str())
    }
}

#[cfg(feature = "http")]
impl Read for HttpReadStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.body_reader.read(buf)
    }
}

#[cfg(feature = "http")]
pub struct HttpWriteStream {
    status_code: u16,
    headers: std::mem::ManuallyDrop<hyper::HeaderMap>,
    response: TypedArenaPtr<HttpResponse>,
    buffer: std::mem::ManuallyDrop<Vec<u8>>,
}

#[cfg(feature = "http")]
impl Debug for HttpWriteStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Http Write Stream")
    }
}

#[cfg(feature = "http")]
impl Write for HttpWriteStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.buffer.extend_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(feature = "http")]
impl HttpWriteStream {
    // TODO why is this suddenly dead code and should it be used somewhere?
    // Should this be impl Drop for HttpWriteStream?
    #[allow(dead_code)]
    fn drop(&mut self) {
        let headers = unsafe { std::mem::ManuallyDrop::take(&mut self.headers) };
        let buffer = unsafe { std::mem::ManuallyDrop::take(&mut self.buffer) };

        let (ready, response, cvar) = &**self.response;

        let mut ready = ready.lock().unwrap();
        {
            let mut response = response.lock().unwrap();

            let mut response_ = warp::http::Response::builder().status(self.status_code);
            *response_.headers_mut().unwrap() = headers;
            *response = Some(response_.body(warp::hyper::Body::from(buffer)).unwrap());
        }
        *ready = true;
        cvar.notify_one();
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

pub type Callback = Box<dyn FnMut(&mut Cursor<Vec<u8>>)>;

pub struct CallbackStream {
    pub(crate) inner: Cursor<Vec<u8>>,
    callback: Callback,
}

impl Debug for CallbackStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CallbackStream")
            .field("inner", &self.inner)
            .finish()
    }
}

impl Write for CallbackStream {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let pos = self.inner.position();

        self.inner.seek(SeekFrom::End(0))?;
        let result = self.inner.write(buf);
        self.inner.seek(SeekFrom::Start(pos))?;

        result
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        (self.callback)(&mut self.inner);
        self.inner.flush()
    }
}

#[derive(Debug)]
pub struct InputChannelStream {
    pub(crate) inner: Cursor<Vec<u8>>,
    pub eof: bool,
    channel: Receiver<Vec<u8>>,
}

impl Read for InputChannelStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if self.eof {
            return Ok(0);
        }

        let to_read = buf.len();
        let mut total_read = 0;

        loop {
            total_read += self.inner.read(&mut buf[total_read..])?;

            if total_read < to_read {
                // We need to get more data to read
                match self.channel.try_recv() {
                    Ok(data) => {
                        // Append into self.inner
                        let pos = self.inner.position();
                        assert_eq!(pos as usize, self.inner.get_ref().len());
                        self.inner.write_all(&data)?;
                        self.inner.seek(SeekFrom::Start(pos))?;
                    }
                    Err(TryRecvError::Empty) => {
                        // Data is pending
                        break;
                    }
                    Err(TryRecvError::Disconnected) => {
                        // The other end of the channel was closed so we are EOF
                        self.eof = true;
                        break;
                    }
                }
            } else {
                assert_eq!(total_read, to_read);
                break;
            }
        }
        Ok(total_read)
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
            Some(Atom::from(self.alias()))
        } else {
            None
        }
    }

    #[inline]
    pub fn set_alias_to_atom_opt(&mut self, alias: Option<Atom>) {
        self.set_has_alias(alias.is_some());

        if let Some(alias) = alias {
            self.set_alias(alias.index);
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
        impl $crate::arena::AllocateInArena<$stream_tag> for StreamLayout<$stream_type> {
            fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<$stream_tag> {
                $stream_tag::alloc(arena, core::mem::ManuallyDrop::new(self))
            }
        }

        impl ArenaAllocated for $stream_tag {
            type Payload = core::mem::ManuallyDrop<StreamLayout<$stream_type>>;

            #[inline]
            fn tag() -> ArenaHeaderTag {
                ArenaHeaderTag::$stream_tag
            }

            unsafe fn dealloc(ptr: std::ptr::NonNull<TypedAllocSlab<Self>>) {
                let mut slab = unsafe { Box::from_raw(ptr.as_ptr()) };

                match slab.tag() {
                    ArenaHeaderTag::$stream_tag => {
                        unsafe { std::mem::ManuallyDrop::drop(slab.payload()) };
                    }
                    ArenaHeaderTag::Dropped => {}
                    _ => {
                        unreachable!()
                    }
                }
                drop(slab);
            }
        }
    };
}

arena_allocated_impl_for_stream!(CharReader<ByteStream>, ByteStream);
arena_allocated_impl_for_stream!(CharReader<InputFileStream>, InputFileStream);
arena_allocated_impl_for_stream!(OutputFileStream, OutputFileStream);
arena_allocated_impl_for_stream!(CharReader<NamedTcpStream>, NamedTcpStream);
#[cfg(feature = "tls")]
arena_allocated_impl_for_stream!(CharReader<NamedTlsStream>, NamedTlsStream);
#[cfg(feature = "http")]
arena_allocated_impl_for_stream!(CharReader<HttpReadStream>, HttpReadStream);
#[cfg(feature = "http")]
arena_allocated_impl_for_stream!(CharReader<HttpWriteStream>, HttpWriteStream);
arena_allocated_impl_for_stream!(ReadlineStream, ReadlineStream);
arena_allocated_impl_for_stream!(StaticStringStream, StaticStringStream);
arena_allocated_impl_for_stream!(StandardOutputStream, StandardOutputStream);
arena_allocated_impl_for_stream!(StandardErrorStream, StandardErrorStream);
arena_allocated_impl_for_stream!(CharReader<CallbackStream>, CallbackStream);
arena_allocated_impl_for_stream!(CharReader<InputChannelStream>, InputChannelStream);
arena_allocated_impl_for_stream!(CharReader<PipeReader>, PipeReader);
arena_allocated_impl_for_stream!(CharReader<PipeWriter>, PipeWriter);

#[derive(Debug, Copy, Clone)]
pub enum Stream {
    Byte(TypedArenaPtr<ByteStream>),
    InputFile(TypedArenaPtr<InputFileStream>),
    OutputFile(TypedArenaPtr<OutputFileStream>),
    StaticString(TypedArenaPtr<StaticStringStream>),
    NamedTcp(TypedArenaPtr<NamedTcpStream>),
    #[cfg(feature = "tls")]
    NamedTls(TypedArenaPtr<NamedTlsStream>),
    #[cfg(feature = "http")]
    HttpRead(TypedArenaPtr<HttpReadStream>),
    #[cfg(feature = "http")]
    HttpWrite(TypedArenaPtr<HttpWriteStream>),
    Null(StreamOptions),
    Readline(TypedArenaPtr<ReadlineStream>),
    StandardOutput(TypedArenaPtr<StandardOutputStream>),
    StandardError(TypedArenaPtr<StandardErrorStream>),
    Callback(TypedArenaPtr<CallbackStream>),
    InputChannel(TypedArenaPtr<InputChannelStream>),
    PipeReader(TypedArenaPtr<PipeReader>),
    PipeWriter(TypedArenaPtr<PipeWriter>),
}

impl From<TypedArenaPtr<ReadlineStream>> for Stream {
    #[inline]
    fn from(stream: TypedArenaPtr<ReadlineStream>) -> Stream {
        Stream::Readline(stream)
    }
}

impl Stream {
    #[inline]
    pub fn from_owned_string(string: String, arena: &mut Arena) -> Stream {
        Stream::Byte(arena_alloc!(
            StreamLayout::new(CharReader::new(ByteStream(Cursor::new(
                string.into_bytes()
            )))),
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
    pub fn input_channel(channel: Receiver<Vec<u8>>, arena: &mut Arena) -> Stream {
        let inner = Cursor::new(Vec::new());
        Stream::InputChannel(arena_alloc!(
            StreamLayout::new(CharReader::new(InputChannelStream {
                inner,
                eof: false,
                channel
            })),
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

    pub fn from_tag(tag: ArenaHeaderTag, ptr: UntypedArenaPtr) -> Self {
        match tag {
            ArenaHeaderTag::ByteStream => Stream::Byte(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::InputFileStream => Stream::InputFile(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::OutputFileStream => Stream::OutputFile(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::NamedTcpStream => Stream::NamedTcp(unsafe { ptr.as_typed_ptr() }),
            #[cfg(feature = "tls")]
            ArenaHeaderTag::NamedTlsStream => Stream::NamedTls(unsafe { ptr.as_typed_ptr() }),
            #[cfg(feature = "http")]
            ArenaHeaderTag::HttpReadStream => Stream::HttpRead(unsafe { ptr.as_typed_ptr() }),
            #[cfg(feature = "http")]
            ArenaHeaderTag::HttpWriteStream => Stream::HttpWrite(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::ReadlineStream => Stream::Readline(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::StaticStringStream => {
                Stream::StaticString(unsafe { ptr.as_typed_ptr() })
            }
            ArenaHeaderTag::StandardOutputStream => {
                Stream::StandardOutput(unsafe { ptr.as_typed_ptr() })
            }
            ArenaHeaderTag::StandardErrorStream => {
                Stream::StandardError(unsafe { ptr.as_typed_ptr() })
            }
            ArenaHeaderTag::Dropped | ArenaHeaderTag::NullStream => {
                Stream::Null(StreamOptions::default())
            }
            ArenaHeaderTag::CallbackStream => Stream::Callback(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::InputChannelStream => {
                Stream::InputChannel(unsafe { ptr.as_typed_ptr() })
            }
            ArenaHeaderTag::PipeReader => Stream::PipeReader(unsafe { ptr.as_typed_ptr() }),
            ArenaHeaderTag::PipeWriter => Stream::PipeWriter(unsafe { ptr.as_typed_ptr() }),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn is_stderr(&self) -> bool {
        matches!(self, Stream::StandardError(_))
    }

    #[inline]
    pub fn is_stdout(&self) -> bool {
        matches!(self, Stream::StandardOutput(_))
    }

    #[inline]
    pub fn is_stdin(&self) -> bool {
        matches!(self, Stream::Readline(_))
    }

    pub fn as_ptr(&self) -> *const ArenaHeader {
        match self {
            Stream::Byte(ptr) => ptr.header_ptr(),
            Stream::InputFile(ptr) => ptr.header_ptr(),
            Stream::OutputFile(ptr) => ptr.header_ptr(),
            Stream::StaticString(ptr) => ptr.header_ptr(),
            Stream::NamedTcp(ptr) => ptr.header_ptr(),
            #[cfg(feature = "tls")]
            Stream::NamedTls(ptr) => ptr.header_ptr(),
            #[cfg(feature = "http")]
            Stream::HttpRead(ptr) => ptr.header_ptr(),
            #[cfg(feature = "http")]
            Stream::HttpWrite(ptr) => ptr.header_ptr(),
            Stream::Null(_) => ptr::null(),
            Stream::Readline(ptr) => ptr.header_ptr(),
            Stream::StandardOutput(ptr) => ptr.header_ptr(),
            Stream::StandardError(ptr) => ptr.header_ptr(),
            Stream::Callback(ptr) => ptr.header_ptr(),
            Stream::InputChannel(ptr) => ptr.header_ptr(),
            Stream::PipeReader(ptr) => ptr.header_ptr(),
            Stream::PipeWriter(ptr) => ptr.header_ptr(),
        }
    }

    pub fn options(&self) -> &StreamOptions {
        match self {
            Stream::Byte(ref ptr) => &ptr.options,
            Stream::InputFile(ref ptr) => &ptr.options,
            Stream::OutputFile(ref ptr) => &ptr.options,
            Stream::StaticString(ref ptr) => &ptr.options,
            Stream::NamedTcp(ref ptr) => &ptr.options,
            #[cfg(feature = "tls")]
            Stream::NamedTls(ref ptr) => &ptr.options,
            #[cfg(feature = "http")]
            Stream::HttpRead(ref ptr) => &ptr.options,
            #[cfg(feature = "http")]
            Stream::HttpWrite(ref ptr) => &ptr.options,
            Stream::Null(ref options) => options,
            Stream::Readline(ref ptr) => &ptr.options,
            Stream::StandardOutput(ref ptr) => &ptr.options,
            Stream::StandardError(ref ptr) => &ptr.options,
            Stream::Callback(ref ptr) => &ptr.options,
            Stream::InputChannel(ref ptr) => &ptr.options,
            Stream::PipeReader(ref ptr) => &ptr.options,
            Stream::PipeWriter(ref ptr) => &ptr.options,
        }
    }

    pub(super) fn options_mut(&mut self) -> &mut StreamOptions {
        match self {
            Stream::Byte(ref mut ptr) => &mut ptr.options,
            Stream::InputFile(ref mut ptr) => &mut ptr.options,
            Stream::OutputFile(ref mut ptr) => &mut ptr.options,
            Stream::StaticString(ref mut ptr) => &mut ptr.options,
            Stream::NamedTcp(ref mut ptr) => &mut ptr.options,
            #[cfg(feature = "tls")]
            Stream::NamedTls(ref mut ptr) => &mut ptr.options,
            #[cfg(feature = "http")]
            Stream::HttpRead(ref mut ptr) => &mut ptr.options,
            #[cfg(feature = "http")]
            Stream::HttpWrite(ref mut ptr) => &mut ptr.options,
            Stream::Null(ref mut options) => options,
            Stream::Readline(ref mut ptr) => &mut ptr.options,
            Stream::StandardOutput(ref mut ptr) => &mut ptr.options,
            Stream::StandardError(ref mut ptr) => &mut ptr.options,
            Stream::Callback(ref mut ptr) => &mut ptr.options,
            Stream::InputChannel(ref mut ptr) => &mut ptr.options,
            Stream::PipeReader(ref mut ptr) => &mut ptr.options,
            Stream::PipeWriter(ref mut ptr) => &mut ptr.options,
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
            #[cfg(feature = "tls")]
            Stream::NamedTls(ptr) => ptr.lines_read += incr_num_lines_read,
            #[cfg(feature = "http")]
            Stream::HttpRead(ptr) => ptr.lines_read += incr_num_lines_read,
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => {}
            Stream::Null(_) => {}
            Stream::Readline(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::StandardOutput(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::StandardError(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::Callback(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::InputChannel(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::PipeReader(ptr) => ptr.lines_read += incr_num_lines_read,
            Stream::PipeWriter(_) => {}
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
            #[cfg(feature = "tls")]
            Stream::NamedTls(ptr) => ptr.lines_read = value,
            #[cfg(feature = "http")]
            Stream::HttpRead(ptr) => ptr.lines_read = value,
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => {}
            Stream::Null(_) => {}
            Stream::Readline(ptr) => ptr.lines_read = value,
            Stream::StandardOutput(ptr) => ptr.lines_read = value,
            Stream::StandardError(ptr) => ptr.lines_read = value,
            Stream::Callback(ptr) => ptr.lines_read = value,
            Stream::InputChannel(ptr) => ptr.lines_read = value,
            Stream::PipeReader(ptr) => ptr.lines_read = value,
            Stream::PipeWriter(_) => {}
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
            #[cfg(feature = "tls")]
            Stream::NamedTls(ptr) => ptr.lines_read,
            #[cfg(feature = "http")]
            Stream::HttpRead(ptr) => ptr.lines_read,
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => 0,
            Stream::Null(_) => 0,
            Stream::Readline(ptr) => ptr.lines_read,
            Stream::StandardOutput(ptr) => ptr.lines_read,
            Stream::StandardError(ptr) => ptr.lines_read,
            Stream::Callback(ptr) => ptr.lines_read,
            Stream::InputChannel(ptr) => ptr.lines_read,
            Stream::PipeReader(ptr) => ptr.lines_read,
            Stream::PipeWriter(_) => 0,
        }
    }
}

impl CharRead for Stream {
    fn peek_char(&mut self) -> Option<std::io::Result<char>> {
        match self {
            Stream::InputFile(file) => (*file).peek_char(),
            Stream::NamedTcp(tcp_stream) => (*tcp_stream).peek_char(),
            #[cfg(feature = "tls")]
            Stream::NamedTls(tls_stream) => (*tls_stream).peek_char(),
            #[cfg(feature = "http")]
            Stream::HttpRead(http_stream) => (*http_stream).peek_char(),
            Stream::Readline(rl_stream) => (*rl_stream).peek_char(),
            Stream::StaticString(src) => (*src).peek_char(),
            Stream::Byte(cursor) => (*cursor).peek_char(),
            Stream::InputChannel(cursor) => (*cursor).peek_char(),
            Stream::PipeReader(cursor) => (*cursor).peek_char(),

            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => Some(Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            ))),
            Stream::OutputFile(_)
            | Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::Null(_)
            | Stream::Callback(_)
            | Stream::PipeWriter(_) => Some(Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            ))),
        }
    }

    fn read_char(&mut self) -> Option<std::io::Result<char>> {
        match self {
            Stream::InputFile(file) => (*file).read_char(),
            Stream::NamedTcp(tcp_stream) => (*tcp_stream).read_char(),
            #[cfg(feature = "tls")]
            Stream::NamedTls(tls_stream) => (*tls_stream).read_char(),
            #[cfg(feature = "http")]
            Stream::HttpRead(http_stream) => (*http_stream).read_char(),
            Stream::Readline(rl_stream) => (*rl_stream).read_char(),
            Stream::StaticString(src) => (*src).read_char(),
            Stream::Byte(cursor) => (*cursor).read_char(),
            Stream::InputChannel(cursor) => (*cursor).read_char(),
            Stream::PipeReader(cursor) => (*cursor).read_char(),
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => Some(Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            ))),
            Stream::OutputFile(_)
            | Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::Null(_)
            | Stream::Callback(_)
            | Stream::PipeWriter(_) => Some(Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            ))),
        }
    }

    fn put_back_char(&mut self, c: char) {
        match self {
            Stream::InputFile(file) => file.put_back_char(c),
            Stream::NamedTcp(tcp_stream) => tcp_stream.put_back_char(c),
            #[cfg(feature = "tls")]
            Stream::NamedTls(tls_stream) => tls_stream.put_back_char(c),
            #[cfg(feature = "http")]
            Stream::HttpRead(http_stream) => http_stream.put_back_char(c),
            Stream::Readline(rl_stream) => rl_stream.put_back_char(c),
            Stream::StaticString(src) => src.put_back_char(c),
            Stream::Byte(cursor) => cursor.put_back_char(c),
            Stream::PipeReader(cursor) => cursor.put_back_char(c),
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => {}
            Stream::OutputFile(_)
            | Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::Null(_)
            | Stream::Callback(_)
            | Stream::PipeWriter(_) => {}
            Stream::InputChannel(_) => {}
        }
    }

    fn consume(&mut self, nread: usize) {
        match self {
            Stream::InputFile(ref mut file) => file.consume(nread),
            Stream::NamedTcp(ref mut tcp_stream) => tcp_stream.consume(nread),
            #[cfg(feature = "tls")]
            Stream::NamedTls(ref mut tls_stream) => tls_stream.consume(nread),
            #[cfg(feature = "http")]
            Stream::HttpRead(ref mut http_stream) => http_stream.consume(nread),
            Stream::Readline(ref mut rl_stream) => rl_stream.consume(nread),
            Stream::StaticString(ref mut src) => src.consume(nread),
            Stream::Byte(ref mut cursor) => cursor.consume(nread),
            Stream::InputChannel(ref mut cursor) => cursor.consume(nread),
            Stream::PipeReader(ref mut cursor) => cursor.consume(nread),
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => {}
            Stream::OutputFile(_)
            | Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::Null(_)
            | Stream::Callback(_)
            | Stream::PipeWriter(_) => {}
        }
    }
}

impl Read for Stream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self {
            Stream::InputFile(file) => (*file).read(buf),
            Stream::NamedTcp(tcp_stream) => (*tcp_stream).read(buf),
            #[cfg(feature = "tls")]
            Stream::NamedTls(tls_stream) => (*tls_stream).read(buf),
            #[cfg(feature = "http")]
            Stream::HttpRead(http_stream) => (*http_stream).read(buf),
            Stream::Readline(rl_stream) => (*rl_stream).read(buf),
            Stream::StaticString(src) => (*src).read(buf),
            Stream::Byte(cursor) => (*cursor).read(buf),
            Stream::InputChannel(cursor) => (*cursor).read(buf),
            Stream::PipeReader(cursor) => (*cursor).read(buf),
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            )),
            Stream::OutputFile(_)
            | Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::Callback(_)
            | Stream::PipeWriter(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::ReadFromOutputStream,
            )),
            Stream::Null(_) => Ok(0),
        }
    }
}

impl Write for Stream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Stream::OutputFile(ref mut file) => file.write(buf),
            Stream::NamedTcp(ref mut tcp_stream) => tcp_stream.get_mut().write(buf),
            #[cfg(feature = "tls")]
            Stream::NamedTls(ref mut tls_stream) => tls_stream.get_mut().write(buf),
            Stream::Byte(ref mut cursor) => cursor.get_mut().write(buf),
            Stream::Callback(ref mut callback_stream) => callback_stream.get_mut().write(buf),
            Stream::StandardOutput(stream) => stream.write(buf),
            Stream::StandardError(stream) => stream.write(buf),
            #[cfg(feature = "http")]
            Stream::HttpWrite(ref mut stream) => stream.get_mut().write(buf),
            Stream::PipeWriter(ref mut stream) => stream.get_mut().write(buf),
            #[cfg(feature = "http")]
            Stream::HttpRead(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::WriteToInputStream,
            )),
            Stream::Null(_) => Ok(buf.len()),
            Stream::StaticString(_)
            | Stream::InputChannel(_)
            | Stream::Readline(_)
            | Stream::InputFile(..)
            | Stream::PipeReader(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::WriteToInputStream,
            )),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Stream::OutputFile(ref mut file) => file.stream.flush(),
            Stream::NamedTcp(ref mut tcp_stream) => tcp_stream.stream.get_mut().flush(),
            #[cfg(feature = "tls")]
            Stream::NamedTls(ref mut tls_stream) => tls_stream.stream.get_mut().flush(),
            Stream::Byte(ref mut cursor) => cursor.stream.get_mut().flush(),
            Stream::Callback(ref mut callback_stream) => callback_stream.stream.get_mut().flush(),
            Stream::StandardError(stream) => stream.stream.flush(),
            Stream::StandardOutput(stream) => stream.stream.flush(),
            Stream::PipeWriter(ref mut stream) => stream.stream.get_mut().flush(),
            #[cfg(feature = "http")]
            Stream::HttpWrite(ref mut stream) => stream.stream.get_mut().flush(),
            #[cfg(feature = "http")]
            Stream::HttpRead(_) => Err(std::io::Error::new(
                ErrorKind::PermissionDenied,
                StreamError::FlushToInputStream,
            )),
            Stream::Null(_) => Ok(()),
            Stream::StaticString(_)
            | Stream::InputChannel(_)
            | Stream::Readline(_)
            | Stream::InputFile(_)
            | Stream::PipeReader(_) => Err(std::io::Error::new(
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
    #[allow(unused)]
    PeekCharFailed,
    #[allow(unused)]
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

fn cursor_position<T>(
    past_end_of_stream: &mut bool,
    cursor: &Cursor<T>,
    cursor_len: u64,
) -> AtEndOfStream {
    match cursor.position().cmp(&cursor_len) {
        Ordering::Equal => AtEndOfStream::At,
        Ordering::Greater => {
            *past_end_of_stream = true;
            AtEndOfStream::Past
        }
        Ordering::Less => AtEndOfStream::Not,
    }
}

impl From<Stream> for HeapCellValue {
    #[inline(always)]
    fn from(stream: Stream) -> Self {
        if stream.is_null_stream() {
            let res = atom!("null_stream");
            atom_as_cell!(res)
        } else {
            let res = stream.as_ptr();
            debug_assert!(!res.is_null());
            raw_ptr_as_cell!(res)
        }
    }
}

impl Stream {
    #[inline]
    pub(crate) fn position(&mut self) -> Option<(u64, usize)> {
        // returns lines_read, position.
        let result = match self {
            Stream::Byte(byte_stream_layout) => {
                Some(byte_stream_layout.stream.get_ref().0.position())
            }
            Stream::StaticString(string_stream_layout) => {
                Some(string_stream_layout.stream.stream.position())
            }
            Stream::InputFile(file_stream) => file_stream.position(),
            #[cfg(feature = "tls")]
            Stream::NamedTls(..) => Some(0),
            Stream::NamedTcp(..) | Stream::Readline(..) => Some(0),
            _ => None,
        };

        result.map(|position| (position, self.lines_read()))
    }

    #[inline]
    pub(crate) fn set_position(&mut self, position: u64) {
        if let Stream::InputFile(stream_layout) = self {
            let StreamLayout {
                past_end_of_stream,
                stream,
                ..
            } = &mut ***stream_layout;

            stream
                .get_mut()
                .file
                .seek(SeekFrom::Start(position))
                .unwrap();
            stream.reset_buffer(); // flush the internal buffer.

            if let Ok(metadata) = stream.get_ref().file.metadata() {
                *past_end_of_stream = position > metadata.len();
            }
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
            #[cfg(feature = "tls")]
            Stream::NamedTls(stream) => stream.past_end_of_stream,
            #[cfg(feature = "http")]
            Stream::HttpRead(stream) => stream.past_end_of_stream,
            #[cfg(feature = "http")]
            Stream::HttpWrite(stream) => stream.past_end_of_stream,
            Stream::Null(_) => false,
            Stream::Readline(stream) => stream.past_end_of_stream,
            Stream::StandardOutput(stream) => stream.past_end_of_stream,
            Stream::StandardError(stream) => stream.past_end_of_stream,
            Stream::Callback(stream) => stream.past_end_of_stream,
            Stream::InputChannel(stream) => stream.past_end_of_stream,
            Stream::PipeReader(stream) => stream.past_end_of_stream,
            Stream::PipeWriter(stream) => stream.past_end_of_stream,
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
            #[cfg(feature = "tls")]
            Stream::NamedTls(stream) => stream.past_end_of_stream = value,
            #[cfg(feature = "http")]
            Stream::HttpRead(stream) => stream.past_end_of_stream = value,
            #[cfg(feature = "http")]
            Stream::HttpWrite(stream) => stream.past_end_of_stream = value,
            Stream::Null(_) => {}
            Stream::Readline(stream) => stream.past_end_of_stream = value,
            Stream::StandardOutput(stream) => stream.past_end_of_stream = value,
            Stream::StandardError(stream) => stream.past_end_of_stream = value,
            Stream::Callback(stream) => stream.past_end_of_stream = value,
            Stream::InputChannel(stream) => stream.past_end_of_stream = value,
            Stream::PipeReader(stream) => stream.past_end_of_stream = value,
            Stream::PipeWriter(stream) => stream.past_end_of_stream = value,
        }
    }

    #[inline]
    pub(crate) fn position_relative_to_end(&mut self) -> AtEndOfStream {
        if self.past_end_of_stream() {
            return AtEndOfStream::Past;
        }

        match self {
            Stream::Byte(stream_layout) => {
                let StreamLayout {
                    past_end_of_stream,
                    stream,
                    ..
                } = &mut ***stream_layout;

                let cursor_len = stream.get_ref().0.get_ref().len() as u64;
                cursor_position(past_end_of_stream, &stream.get_ref().0, cursor_len)
            }
            Stream::StaticString(stream_layout) => {
                let StreamLayout {
                    past_end_of_stream,
                    stream,
                    ..
                } = &mut ***stream_layout;

                let cursor_len = stream.stream.get_ref().len() as u64;
                cursor_position(past_end_of_stream, &stream.stream, cursor_len)
            }
            Stream::InputFile(stream_layout) => {
                let position = stream_layout.position();

                let StreamLayout {
                    past_end_of_stream,
                    stream,
                    ..
                } = &mut ***stream_layout;

                match stream.get_ref().file.metadata() {
                    Ok(metadata) => {
                        if let Some(position) = position {
                            match position.cmp(&metadata.len()) {
                                Ordering::Equal => AtEndOfStream::At,
                                Ordering::Less => AtEndOfStream::Not,
                                Ordering::Greater => {
                                    *past_end_of_stream = true;
                                    AtEndOfStream::Past
                                }
                            }
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
            }
            Stream::Null(_) => AtEndOfStream::At,
            #[cfg(feature = "http")]
            Stream::HttpRead(stream_layout) => {
                if stream_layout
                    .stream
                    .get_ref()
                    .body_reader
                    .get_ref()
                    .has_remaining()
                {
                    AtEndOfStream::Not
                } else {
                    AtEndOfStream::Past
                }
            }
            Stream::InputChannel(stream_layout) => {
                if stream_layout.stream.get_ref().eof {
                    AtEndOfStream::At
                } else {
                    AtEndOfStream::Not
                }
            }
            _ => AtEndOfStream::Not,
        }
    }

    #[inline]
    pub(crate) fn file_name(&self) -> Option<Atom> {
        match self {
            Stream::InputFile(file) => Some(file.stream.get_ref().file_name),
            Stream::OutputFile(file) => Some(file.stream.file_name),
            Stream::NamedTcp(tcp) => Some(tcp.stream.get_ref().address),
            #[cfg(feature = "tls")]
            Stream::NamedTls(tls) => Some(tls.stream.get_ref().address),
            _ => None,
        }
    }

    #[inline]
    pub(crate) fn mode(&self) -> Atom {
        match self {
            #[cfg(feature = "http")]
            Stream::HttpRead(_) => atom!("read"),
            #[cfg(feature = "tls")]
            Stream::NamedTls(..) => atom!("read_append"),
            Stream::Byte(_)
            | Stream::InputChannel(_)
            | Stream::Readline(_)
            | Stream::StaticString(_)
            | Stream::InputFile(..)
            | Stream::PipeReader(_) => atom!("read"),
            Stream::NamedTcp(..) => atom!("read_append"),
            Stream::OutputFile(file) if file.is_append => atom!("append"),
            #[cfg(feature = "http")]
            Stream::HttpWrite(_) => atom!("write"),
            Stream::OutputFile(_)
            | Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::Callback(_)
            | Stream::PipeWriter(_) => {
                atom!("write")
            }
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
    pub fn from_callback(callback: Callback, arena: &mut Arena) -> Self {
        Stream::Callback(arena_alloc!(
            ManuallyDrop::new(StreamLayout::new(CharReader::new(CallbackStream {
                inner: Cursor::new(Vec::new()),
                callback,
            }))),
            arena
        ))
    }

    pub(crate) fn from_pipe_writer(writer: PipeWriter, arena: &mut Arena) -> Stream {
        Stream::PipeWriter(arena_alloc!(
            ManuallyDrop::new(StreamLayout::new(CharReader::new(writer))),
            arena
        ))
    }

    pub(crate) fn from_pipe_reader(reader: PipeReader, arena: &mut Arena) -> Stream {
        Stream::PipeReader(arena_alloc!(
            ManuallyDrop::new(StreamLayout::new(CharReader::new(reader))),
            arena
        ))
    }

    #[inline]
    pub(crate) fn from_tcp_stream(address: Atom, tcp_stream: TcpStream, arena: &mut Arena) -> Self {
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

    #[cfg(feature = "tls")]
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

    #[cfg(feature = "http")]
    #[inline]
    pub(crate) fn from_http_stream(
        url: Atom,
        http_stream: BufReader<Bytes>,
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

    #[cfg(feature = "http")]
    #[inline]
    pub(crate) fn from_http_sender(
        response: TypedArenaPtr<HttpResponse>,
        status_code: u16,
        headers: hyper::HeaderMap,
        arena: &mut Arena,
    ) -> Self {
        Stream::HttpWrite(arena_alloc!(
            StreamLayout::new(CharReader::new(HttpWriteStream {
                response,
                status_code,
                headers: std::mem::ManuallyDrop::new(headers),
                buffer: std::mem::ManuallyDrop::new(Vec::new()),
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

    /// Drops the stream handle and marks the arena pointer as [`ArenaHeaderTag::Dropped`].
    #[inline]
    pub(crate) fn close(&mut self) -> Result<(), std::io::Error> {
        match self {
            Stream::NamedTcp(ref mut tcp_stream) => {
                tcp_stream.inner_mut().tcp_stream.shutdown(Shutdown::Both)
            }
            #[cfg(feature = "tls")]
            Stream::NamedTls(ref mut tls_stream) => tls_stream.inner_mut().tls_stream.shutdown(),
            #[cfg(feature = "http")]
            Stream::HttpRead(ref mut http_stream) => {
                http_stream.drop_payload();

                Ok(())
            }
            #[cfg(feature = "http")]
            Stream::HttpWrite(mut http_stream) => {
                http_stream.drop_payload();

                Ok(())
            }
            Stream::InputFile(mut file_stream) => {
                // close the stream by dropping the inner File.
                file_stream.drop_payload();

                Ok(())
            }
            Stream::OutputFile(mut file_stream) => {
                // close the stream by dropping the inner File.
                file_stream.drop_payload();

                Ok(())
            }
            Stream::Byte(mut stream) => {
                stream.drop_payload();
                Ok(())
            }
            Stream::Callback(mut stream) => {
                stream.drop_payload();
                Ok(())
            }
            Stream::InputChannel(mut stream) => {
                stream.drop_payload();
                Ok(())
            }
            Stream::StaticString(mut stream) => {
                stream.drop_payload();
                Ok(())
            }

            Stream::PipeReader(mut stream) => {
                stream.drop_payload();
                Ok(())
            }

            Stream::PipeWriter(mut stream) => {
                stream.drop_payload();
                Ok(())
            }

            Stream::Null(_) => Ok(()),

            Stream::Readline(_) | Stream::StandardOutput(_) | Stream::StandardError(_) => {
                unreachable!();
            }
        }
    }

    #[inline]
    pub(crate) fn is_null_stream(&self) -> bool {
        matches!(self, Stream::Null(_))
    }

    #[inline]
    pub(crate) fn is_input_stream(&self) -> bool {
        match self {
            #[cfg(feature = "tls")]
            Stream::NamedTls(..) => true,
            #[cfg(feature = "http")]
            Stream::HttpRead(..) => true,
            Stream::NamedTcp(..)
            | Stream::Byte(_)
            | Stream::InputChannel(_)
            | Stream::Readline(_)
            | Stream::StaticString(_)
            | Stream::InputFile(..)
            | Stream::PipeReader(_)
            | Stream::Null(_) => true,
            _ => false,
        }
    }

    #[inline]
    pub(crate) fn is_output_stream(&self) -> bool {
        match self {
            #[cfg(feature = "tls")]
            Stream::NamedTls(..) => true,
            #[cfg(feature = "http")]
            Stream::HttpWrite(..) => true,
            Stream::StandardError(_)
            | Stream::StandardOutput(_)
            | Stream::NamedTcp(..)
            | Stream::Byte(_)
            | Stream::OutputFile(..)
            | Stream::Callback(_)
            | Stream::PipeWriter(_)
            | Stream::Null(_) => true,
            _ => false,
        }
    }

    // returns true on success.
    #[inline]
    pub(super) fn reset(&mut self) -> bool {
        self.set_lines_read(0);
        self.set_past_end_of_stream(false);

        match self {
            Stream::Byte(ref mut cursor) => {
                cursor.stream.get_mut().0.set_position(0);
                true
            }
            Stream::InputFile(ref mut file_stream) => {
                file_stream
                    .stream
                    .get_mut()
                    .file
                    .seek(SeekFrom::Start(0))
                    .unwrap();
                true
            }
            Stream::Readline(ref mut readline_stream) => {
                readline_stream.reset();
                true
            }
            Stream::InputChannel(ref mut input_channel_stream) => {
                input_channel_stream.stream.get_mut().inner.set_position(0);
                true
            }
            _ => false,
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
            Stream::InputFile(ref mut file) => match file.peek_byte() {
                Some(result) => Ok(result?),
                _ => Err(std::io::Error::new(
                    ErrorKind::UnexpectedEof,
                    StreamError::PeekByteFailed,
                )),
            },
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
                Err(self.open_past_eos_error(stream, caller, arity))
            }
            EOFAction::EOFCode => {
                let end_of_stream = if stream.options().stream_type() == StreamType::Binary {
                    fixnum_as_cell!(Fixnum::build_with(-1))
                } else {
                    atom_as_cell!(atom!("end_of_file"))
                };

                stream.set_past_end_of_stream(true);
                unify!(self, result, end_of_stream);
                Ok(())
            }
            EOFAction::Reset => {
                if !stream.reset() {
                    stream.set_past_end_of_stream(true);
                }

                self.fail = stream.past_end_of_stream();
                Ok(())
            }
        }
    }

    /// ## Warning
    ///
    /// The options of streams stored in `Machine::indices` should only
    /// be modified through [`IndexStore::update_stream_options`].
    pub(crate) fn get_stream_options(
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

    /// If `addr` is a [`Cons`](HeapCellValueTag::Cons) to a stream, then returns it.
    ///
    /// If it is an atom or a string, then this searches for the corresponding stream
    /// inside of [`self.indices`], returning it.
    ///
    /// ## Warning
    ///
    /// **Do not directly modify [`stream.options_mut()`](Stream::options_mut)
    /// on the returned stream.**
    ///
    /// Other functions rely on the invariants of [`IndexStore`], which may
    /// become invalidated by the direct modification of a stream's option (namely,
    /// its alias name). Instead, use [`IndexStore::update_stream_options`].
    pub(crate) fn get_stream_or_alias(
        &mut self,
        addr: HeapCellValue,
        indices: &IndexStore,
        caller: Atom,
        arity: usize,
    ) -> Result<Stream, MachineStub> {
        let addr = self.store(MachineState::deref(self, addr));

        read_heap_cell!(addr,
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                return match indices.get_stream(name) {
                    Some(stream) => Ok(stream),
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

                return match indices.get_stream(name) {
                    Some(stream) => Ok(stream),
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
    ) -> Result<Stream, ParserError> {
        match stream.peek_char() {
            None => Ok(stream), // empty stream is handled gracefully by Lexer::eof
            Some(Err(e)) => Err(ParserError::IO(e)),
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
        let err = self.permission_error(
            perm,
            err_atom,
            if let Some(alias) = stream.options().get_alias() {
                atom_as_cell!(alias)
            } else {
                stream.into()
            },
        );

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
        let err = self.permission_error(Permission::Open, atom!("source_sink"), culprit);

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
            functor!(atom!("alias"), [atom_as_cell(alias)]),
        );

        self.error_form(err, stub)
    }

    pub(crate) fn reposition_error(&mut self, stub_name: Atom, stub_arity: usize) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);
        let rep_stub = functor!(atom!("reposition"), [atom_as_cell((atom!("true")))]);
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
        let opt_err = if input.is_some() && !stream.is_input_stream()
            || input.is_none() && !stream.is_output_stream()
        {
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
            let err = self.domain_error(DomainErrorType::SourceSink, self.registers[1]);

            return Err(self.error_form(err, stub));
        }

        // 8.11.5.3l)
        if let Some(alias) = options.get_alias() {
            if indices.has_stream(alias) {
                return Err(self.occupied_alias_permission_error(alias, atom!("open"), 4));
            }
        }

        let mode = cell_as_atom!(self.store(MachineState::deref(self, self.registers[2])));
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

        let mut path = PathBuf::from(&*file_spec.as_str());

        loop {
            let file = match open_options.open(&path) {
                Ok(file) => file,
                Err(err) => {
                    match err.kind() {
                        ErrorKind::NotFound => {
                            // 8.11.5.3j)
                            let stub = functor_stub(atom!("open"), 4);

                            let err =
                                self.existence_error(ExistenceError::SourceSink(self[temp_v!(1)]));

                            return Err(self.error_form(err, stub));
                        }
                        ErrorKind::PermissionDenied => {
                            // 8.11.5.3k)
                            return Err(self.open_permission_error(
                                self.registers[1],
                                atom!("open"),
                                4,
                            ));
                        }
                        _ => {
                            // assume the OS is out of file descriptors.
                            let stub = functor_stub(atom!("open"), 4);
                            let err = Self::resource_error(ResourceError::OutOfFiles);

                            return Err(self.error_form(err, stub));
                        }
                    }
                }
            };

            if path.extension().is_none() {
                if let Ok(metadata) = file.metadata() {
                    if metadata.is_dir() {
                        path.set_extension("pl");
                        continue;
                    }
                }
            }

            return Ok(if is_input_file {
                Stream::from_file_as_input(file_spec, file, &mut self.arena)
            } else {
                Stream::from_file_as_output(file_spec, file, in_append_mode, &mut self.arena)
            });
        }
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use std::{cell::RefCell, io::Read, io::Write, rc::Rc};

    use crate::machine::config::*;
    use crate::LeafAnswer;

    use super::{Stream, StreamOptions};

    fn succeeded<T>(answer: Vec<Result<LeafAnswer, T>>) -> bool {
        // Ideally this should be a method in QueryState or LeafAnswer.
        matches!(
            answer[0].as_ref(),
            Ok(LeafAnswer::True) | Ok(LeafAnswer::LeafAnswer { .. })
        )
    }

    fn is_successful<T>(answer: &Result<LeafAnswer, T>) -> bool {
        matches!(
            answer,
            Ok(LeafAnswer::True) | Ok(LeafAnswer::LeafAnswer { .. })
        )
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn user_input_string_stream() {
        let streams =
            StreamConfig::default().with_user_input(InputStreamConfig::string("a(1,2,3)."));

        let mut machine = MachineBuilder::default().with_streams(streams).build();

        let complete_answer: Vec<_> = machine
            .run_query(r#"current_input(_), \+ at_end_of_stream."#)
            .collect();

        assert!(succeeded(complete_answer));

        let complete_answer: Vec<_> = machine.run_query("read(A).").collect();

        assert_eq!(
            complete_answer,
            [Ok(LeafAnswer::from_bindings([(
                "A",
                Term::compound("a", [Term::integer(1), Term::integer(2), Term::integer(3),])
            )]))]
        );

        let complete_answer: Vec<_> = machine.run_query(r#"at_end_of_stream."#).collect();

        assert!(succeeded(complete_answer));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn user_input_channel_stream() {
        let (mut user_input, channel_stream) = InputStreamConfig::channel();
        let streams = StreamConfig::default().with_user_input(channel_stream);
        let mut machine = MachineBuilder::default().with_streams(streams).build();

        let complete_answer: Vec<_> = machine
            .run_query(r#"current_input(_), \+ at_end_of_stream."#)
            .collect();

        assert!(succeeded(complete_answer));

        write!(user_input, "a(1,2,3).").unwrap();

        let complete_answer: Vec<_> = machine
            .run_query(r#"\+ at_end_of_stream, read(A)."#)
            .collect();

        assert_eq!(
            complete_answer,
            [Ok(LeafAnswer::from_bindings([(
                "A",
                Term::compound("a", [Term::integer(1), Term::integer(2), Term::integer(3),])
            )]))]
        );

        // End-of-data but not end-of-stream;
        let complete_answer: Vec<_> = machine
            .run_query(
                r#"
                use_module(library(charsio)),
                current_input(In), get_n_chars(In, N, C),
                N == 0, \+ at_end_of_stream.
            "#,
            )
            .collect();

        assert!(succeeded(complete_answer));

        // Dropping the sender closes the input
        drop(user_input);

        let complete_answer: Vec<_> = machine
            .run_query(
                r#"
                current_input(In), get_n_chars(In, N, _),
                N == 0, at_end_of_stream.
            "#,
            )
            .collect();

        assert!(succeeded(complete_answer));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn user_output_callback_stream() {
        let test_string = Rc::new(RefCell::new(String::new()));

        let streams =
            StreamConfig::default().with_user_output(OutputStreamConfig::callback(Box::new({
                let test_string = test_string.clone();
                move |x| {
                    x.read_to_string(&mut test_string.borrow_mut()).unwrap();
                }
            })));

        let mut machine = MachineBuilder::default().with_streams(streams).build();

        let complete_answer: Vec<_> = machine
            .run_query(r#"current_output(Out), \+ at_end_of_stream(Out)."#)
            .collect();

        assert!(succeeded(complete_answer));

        let complete_answer: Vec<_> = machine
            .run_query(r#"write(asdf), nl, flush_output."#)
            .collect();

        assert!(succeeded(complete_answer));
        assert_eq!(test_string.borrow().as_str(), "asdf\n");

        let complete_answer: Vec<_> = machine.run_query(r#"write(abcd), flush_output."#).collect();

        assert!(succeeded(complete_answer));
        assert_eq!(test_string.borrow().as_str(), "asdf\nabcd");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_memory_user_output_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query(
                "\\+ \\+ (current_output(Stream), close(Stream)), write(user_output, hello).",
            )
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());

        let mut actual = String::new();
        machine.user_output.read_to_string(&mut actual).unwrap();
        assert_eq!(actual, "hello");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn current_input_null_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine.run_query("current_input(S).").collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(is_successful(&results[0]));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_memory_user_output_stream_twice() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query("\\+ \\+ (current_output(Stream), close(Stream), close(Stream)).")
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn read_null_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine.run_query("get_code(C).").collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(
            is_successful(&results[0]),
            "Expected read to succeed, got {:?}",
            results[0]
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_realiased_stream() {
        let mut machine = MachineBuilder::new().build();

        let results = machine
            .run_query(
                r#"
                \+ \+ (
                    open("README.md", read, S, [alias(readme)]),
                    open(stream(S), read, _, [alias(another_alias)]),
                    close(S)
                ),
                open("README.md", read, _, [alias(readme)]).
            "#,
            )
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn current_output_null_stream() {
        // TODO: switch to a proper solution for configuring the machine with null streams
        // once `StreamConfig` supports it.
        let mut machine = MachineBuilder::new().build();
        machine.user_output = Stream::Null(StreamOptions::default());
        machine.configure_streams();

        let results = machine.run_query("current_output(S).").collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(is_successful(&results[0]));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_realiased_user_output() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query(
                r#"
                \+ \+ (
                    open("README.md", read, S),
                    open(stream(S), read, _, [alias(user_output)]),
                    close(S)
                ),
                write(user_output, hello).
            "#,
            )
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn write_null_stream() {
        // TODO: switch to a proper solution for configuring the machine with null streams
        // once `StreamConfig` supports it.
        let mut machine = MachineBuilder::new().build();
        machine.user_output = Stream::Null(StreamOptions::default());
        machine.configure_streams();

        let results = machine.run_query("write(hello).").collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(
            is_successful(&results[0]),
            "Expected write to succeed, got {:?}",
            results[0]
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn put_code_null_stream() {
        // TODO: switch to a proper solution for configuring the machine with null streams
        // once `StreamConfig` supports it.
        let mut machine = MachineBuilder::new().build();
        machine.user_output = Stream::Null(StreamOptions::default());
        machine.configure_streams();

        let results = machine
            .run_query("put_code(user_output, 65).")
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(
            is_successful(&results[0]),
            "Expected write to succeed, got {:?}",
            results[0]
        );
    }

    /// A variant of the [`write_null_stream`] that tries to write to a (null) input stream.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn write_null_input_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query("current_input(Stream), write(Stream, hello).")
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(
            is_successful(&results[0]),
            "Expected write to succeed, got {:?}",
            results[0]
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn at_end_of_stream_0_null_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine.run_query("at_end_of_stream.").collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(
            is_successful(&results[0]),
            "Expected at_end_of_stream to succeed, got {:?}",
            results[0]
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn at_end_of_stream_1_null_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query("current_input(Stream), at_end_of_stream(Stream).")
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(
            is_successful(&results[0]),
            "Expected at_end_of_stream to succeed, got {:?}",
            results[0]
        );
    }
}
