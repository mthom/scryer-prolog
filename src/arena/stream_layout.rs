use crate::arena::alloc::*;
use crate::arena::opt_in_buf_reader::*;
use crate::arena::read_line::*;
use crate::arena::stream_insts::*;
use crate::atom_table::*;

#[cfg(feature = "http")]
use crate::http::HttpResponse;
use crate::types::*;

use bytes::{Buf, Bytes, buf::Reader as BytesReader};
use compact_str::*;

pub use modular_bitfield::prelude::*;

use std::cmp::Ordering;
use std::fmt;
use std::fmt::Debug;
use std::fs::File;
use std::hash::Hash;
use std::io;
use std::io::{Cursor, PipeReader, PipeWriter, Read, Seek, SeekFrom, Write};
use std::net::*;
use std::ops::{Deref, DerefMut};
use std::sync::mpsc::Receiver;

#[cfg(feature = "tls")]
use native_tls::TlsStream;

#[cfg(feature = "http")]
use warp::hyper;

#[derive(Debug, Specifier, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Specifier, Clone, Copy, PartialEq, Eq, Hash)]
#[bits = 2]
pub enum EOFAction {
    EOFCode,
    Error,
    Reset,
}

#[derive(Debug, Specifier, Copy, Clone, PartialEq)]
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

#[derive(Debug, Clone)]
pub struct StreamLayout<T: ?Sized> {
    pub options: StreamOptions,
    pub lines_read: usize,
    pub past_end_of_stream: bool,
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
        impl $crate::arena::alloc::AllocateInArena<$stream_tag> for StreamLayout<$stream_type> {
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

pub(crate) type NamedTlsStream = NamedTlsStreamTemplate<Stream>;

arena_allocated_impl_for_stream!(ByteStream, ByteStream);
arena_allocated_impl_for_stream!(InputFileStream, InputFileStream);
arena_allocated_impl_for_stream!(OutputFileStream, OutputFileStream);
arena_allocated_impl_for_stream!(BufferedNamedTcpStream, BufferedNamedTcpStream);
#[cfg(feature = "tls")]
arena_allocated_impl_for_stream!(OptInBufReader<NamedTlsStream>, NamedTlsStream);
#[cfg(feature = "http")]
arena_allocated_impl_for_stream!(HttpReadStream, HttpReadStream);
#[cfg(feature = "http")]
arena_allocated_impl_for_stream!(HttpWriteStream, HttpWriteStream);
arena_allocated_impl_for_stream!(StaticStringStream, StaticStringStream);
arena_allocated_impl_for_stream!(StandardOutputStream, StandardOutputStream);
arena_allocated_impl_for_stream!(StandardErrorStream, StandardErrorStream);
arena_allocated_impl_for_stream!(CallbackStream, CallbackStream);
arena_allocated_impl_for_stream!(InputChannelStream, InputChannelStream);
arena_allocated_impl_for_stream!(OptInBufReader<PipeReaderStream>, PipeReaderStream);
arena_allocated_impl_for_stream!(PipeWriterStream, PipeWriterStream);
arena_allocated_impl_for_stream!(ReadlineStream, ReadlineStream);

pub(crate) trait PrologStream: GraphemeRead + Write {
    fn peek_byte(&mut self) -> io::Result<Option<u8>> {
        let buf = self.peek_grapheme(0)?;
        Ok(buf.and_then(|buf| buf.as_bytes().get(0)).cloned())
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream;
    fn mode(&self) -> Atom;

    fn close(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn reset(&mut self) -> bool {
        false
    }

    fn position(&mut self) -> Option<u64> {
        None
    }

    // returns the new position from the start of the stream in bytes
    fn set_position(&mut self, _pos: u64) -> io::Result<u64> {
        Ok(0)
    }

    fn file_name(&self) -> Option<Atom> {
        None
    }
}

impl PrologStream for ByteStream {
    fn reset(&mut self) -> bool {
        self.0.set_position(0);
        true
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        let cursor_len = self.0.get_ref().len() as u64;
        cursor_position(&self.0, cursor_len)
    }

    fn position(&mut self) -> Option<u64> {
        Some(self.0.position())
    }

    fn set_position(&mut self, pos: u64) -> io::Result<u64> {
        self.0.set_position(pos);
        Ok(pos)
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }
}

impl PrologStream for StaticStringStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        let cursor_len = self.stream.get_ref().len() as u64;
        cursor_position(&self.stream, cursor_len)
    }

    fn position(&mut self) -> Option<u64> {
        Some(self.stream.position())
    }

    fn set_position(&mut self, pos: u64) -> io::Result<u64> {
        self.stream.set_position(pos);
        Ok(pos)
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }
}

impl PrologStream for InputFileStream {
    fn reset(&mut self) -> bool {
        if self.set_position(0).is_err() {
            return false;
        }

        true
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        let pos = self.position();

        if let Some(buf) = &self.file.buf
            && (buf.position() as usize) < buf.get_ref().len()
        {
            return AtEndOfStream::Not;
        }

        match self.file.reader().metadata() {
            Ok(metadata) if let Some(pos) = pos => match pos.cmp(&metadata.len()) {
                Ordering::Less => AtEndOfStream::Not,
                Ordering::Equal => AtEndOfStream::At,
                Ordering::Greater => AtEndOfStream::Past,
            },
            _ => AtEndOfStream::Past,
        }
    }

    fn position(&mut self) -> Option<u64> {
        let rem_buf_len = self.file.remaining_buf_len();
        // stream is the internal OptInBufReader. subtract
        // its pending buffer length from position.
        self.file
            .reader_mut()
            .stream_position()
            .map(|pos| pos - rem_buf_len as u64)
            .ok()
    }

    fn set_position(&mut self, pos: u64) -> io::Result<u64> {
        self.file.buf = None;
        self.file.reader_mut().seek(SeekFrom::Start(pos))
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }

    fn file_name(&self) -> Option<Atom> {
        Some(self.file_name)
    }
}

impl PrologStream for OutputFileStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        if self.is_append {
            atom!("append")
        } else {
            atom!("write")
        }
    }

    fn file_name(&self) -> Option<Atom> {
        Some(self.file_name)
    }
}
O
pub struct BufferedNamedTcpStream(OptInBufReader<NamedTcpStream>);

impl Read for BufferedNamedTcpStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

impl Write for BufferedNamedTcpStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

impl GraphemeRead for BufferedNamedTcpStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        self.0.read_grapheme()
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        self.0.peek_grapheme(at)
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        self.0.read_char()
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        self.0.peek_char()
    }
}

impl PrologStream for BufferedNamedTcpStream {
    fn peek_byte(&mut self) -> io::Result<Option<u8>> {
        if self.0.buf.is_none() {
            let mut b = [0u8; 1];
            self.0.reader.tcp_stream.peek(&mut b)?;
            Ok(b.get(0).cloned())
        } else {
            let buf = self.peek_grapheme(0)?;
            Ok(buf.and_then(|buf| buf.as_bytes().get(0)).cloned())
        }
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn close(&mut self) -> io::Result<()> {
        self.0.reader.tcp_stream.shutdown(Shutdown::Both)
    }

    fn position(&mut self) -> Option<u64> {
        Some(0)
    }

    fn mode(&self) -> Atom {
        atom!("read_append")
    }

    fn file_name(&self) -> Option<Atom> {
        Some(self.0.reader.address)
    }
}

#[cfg(feature = "tls")]
impl PrologStream for OptInBufReader<NamedTlsStream> {
    fn close(&mut self) -> io::Result<()> {
        self.reader.tls_stream.shutdown()
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn position(&mut self) -> Option<u64> {
        Some(0)
    }

    fn mode(&self) -> Atom {
        atom!("read_append")
    }

    fn file_name(&self) -> Option<Atom> {
        Some(self.reader.address)
    }
}

impl PrologStream for InputChannelStream {
    fn reset(&mut self) -> bool {
        self.inner.set_position(0);
        true
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        if self.eof {
            AtEndOfStream::At
        } else {
            AtEndOfStream::Not
        }
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }
}

impl PrologStream for OptInBufReader<PipeReaderStream> {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }
}

#[cfg(feature = "http")]
impl PrologStream for HttpReadStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        if self.body_reader.reader().get_ref().has_remaining() {
            AtEndOfStream::Not
        } else {
            AtEndOfStream::Past
        }
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }
}

#[cfg(feature = "http")]
impl PrologStream for HttpWriteStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        atom!("write")
    }
}

impl PrologStream for PipeWriterStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        atom!("write")
    }
}

impl PrologStream for CallbackStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        atom!("write")
    }
}

impl PrologStream for StandardOutputStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        atom!("write")
    }
}

impl PrologStream for StandardErrorStream {
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        AtEndOfStream::Not
    }

    fn mode(&self) -> Atom {
        atom!("write")
    }
}

pub(crate) type StreamPayload = core::mem::ManuallyDrop<StreamLayout<dyn PrologStream>>;

#[derive(Copy, Clone)]
pub(crate) struct Stream(DynamicArenaPtr<StreamPayload>);

impl fmt::Debug for Stream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("DynamicStreamPtr")
            .field(&self.0.as_ptr())
            .finish()
    }
}

impl Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.stream.read(buf)
    }
}

impl Write for Stream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.stream.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.stream.flush()
    }
}

impl GraphemeRead for Stream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        self.stream.read_grapheme()
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        self.stream.peek_grapheme(at)
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        self.stream.read_char()
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        self.stream.peek_char()
    }
}

impl PrologStream for Stream {
    #[inline]
    fn position(&mut self) -> Option<u64> {
        self.stream.position()
    }

    #[inline]
    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        self.stream.position_relative_to_end()
    }

    #[inline]
    fn set_position(&mut self, pos: u64) -> io::Result<u64> {
        self.stream.set_position(pos)
    }

    #[inline]
    fn close(&mut self) -> io::Result<()> {
        self.stream.close()
    }

    #[inline]
    fn reset(&mut self) -> bool {
        self.stream.reset()
    }

    #[inline]
    fn mode(&self) -> Atom {
        self.stream.mode()
    }

    #[inline]
    fn file_name(&self) -> Option<Atom> {
        self.stream.file_name()
    }
}

pub type StreamPtrPayload<T> = core::mem::ManuallyDrop<StreamLayout<T>>;

impl<T: ?Sized + ArenaAllocated> TypedArenaPtr<T> {
    fn into_dynamic_stream<S>(self) -> Stream
    where
        S: PrologStream + 'static,
        T: ArenaAllocated<Payload = StreamPtrPayload<S>>,
    {
        let thin_ptr: *mut StreamPtrPayload<S> = self.as_ptr();
        let fat_ptr: *mut StreamPayload = thin_ptr;

        Stream(unsafe { DynamicArenaPtr::from_raw(self.header_ptr(), fat_ptr) })
    }
}

impl Stream {
    pub(crate) fn as_typed_stream<
        T: PrologStream + ArenaAllocated<Payload = StreamPtrPayload<T>> + 'static,
    >(
        self,
    ) -> Option<TypedArenaPtr<T>> {
        let tag = self.0.tag();

        if tag == T::tag() {
            let fat_ptr: *mut StreamPayload = self.0.as_ptr();
            let thin_ptr: *mut StreamPtrPayload<T> = fat_ptr.cast();

            Some(unsafe { TypedArenaPtr::from_raw(thin_ptr) })
        } else {
            None
        }
    }

    pub(crate) fn from_tag(ptr: UntypedArenaPtr) -> Option<Self> {
        match ptr.get_tag() {
            ArenaHeaderTag::ByteStream => {
                Some(unsafe { ptr.as_typed_ptr::<ByteStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::InputFileStream => {
                Some(unsafe { ptr.as_typed_ptr::<InputFileStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::OutputFileStream => {
                Some(unsafe { ptr.as_typed_ptr::<OutputFileStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::BufferedNamedTcpStream => {
                Some(unsafe { ptr.as_typed_ptr::<BufferedNamedTcpStream>() }.into_dynamic_stream())
            }
            #[cfg(feature = "tls")]
            ArenaHeaderTag::NamedTlsStream => {
                Some(unsafe { ptr.as_typed_ptr::<NamedTlsStream>() }.into_dynamic_stream())
            }
            #[cfg(feature = "http")]
            ArenaHeaderTag::HttpReadStream => {
                Some(unsafe { ptr.as_typed_ptr::<HttpReadStream>() }.into_dynamic_stream())
            }
            #[cfg(feature = "http")]
            ArenaHeaderTag::HttpWriteStream => {
                Some(unsafe { ptr.as_typed_ptr::<HttpWriteStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::ReadlineStream => {
                Some(unsafe { ptr.as_typed_ptr::<ReadlineStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::StaticStringStream => {
                Some(unsafe { ptr.as_typed_ptr::<StaticStringStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::StandardOutputStream => {
                Some(unsafe { ptr.as_typed_ptr::<StandardOutputStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::StandardErrorStream => {
                Some(unsafe { ptr.as_typed_ptr::<StandardErrorStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::CallbackStream => {
                Some(unsafe { ptr.as_typed_ptr::<CallbackStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::InputChannelStream => {
                Some(unsafe { ptr.as_typed_ptr::<InputChannelStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::PipeReaderStream => {
                Some(unsafe { ptr.as_typed_ptr::<PipeReaderStream>() }.into_dynamic_stream())
            }
            ArenaHeaderTag::PipeWriterStream => {
                Some(unsafe { ptr.as_typed_ptr::<PipeWriterStream>() }.into_dynamic_stream())
            }
            _ => None,
        }
    }

    pub(crate) fn as_ptr(self) -> *mut StreamPayload {
        self.0.as_ptr()
    }

    pub(crate) fn is_input_stream(&self) -> bool {
        match self.0.tag() {
            #[cfg(feature = "tls")]
            ArenaHeaderTag::NamedTlsStream => true,
            #[cfg(feature = "http")]
            ArenaHeaderTag::HttpReadStream => true,
            ArenaHeaderTag::BufferedNamedTcpStream
            | ArenaHeaderTag::ByteStream
            | ArenaHeaderTag::InputChannelStream
            | ArenaHeaderTag::ReadlineStream
            | ArenaHeaderTag::StaticStringStream
            | ArenaHeaderTag::InputFileStream
            | ArenaHeaderTag::PipeReaderStream => true,
            _ => false,
        }
    }

    pub(crate) fn is_output_stream(&self) -> bool {
        match self.0.tag() {
            #[cfg(feature = "tls")]
            ArenaHeaderTag::NamedTlsStream => true,
            #[cfg(feature = "http")]
            ArenaHeaderTag::HttpWriteStream => true,
            ArenaHeaderTag::StandardErrorStream
            | ArenaHeaderTag::StandardOutputStream
            | ArenaHeaderTag::BufferedNamedTcpStream
            | ArenaHeaderTag::ByteStream
            | ArenaHeaderTag::OutputFileStream
            | ArenaHeaderTag::CallbackStream
            | ArenaHeaderTag::PipeWriterStream => true,
            _ => false,
        }
    }

    #[inline]
    pub fn is_stdin(&self) -> bool {
        self.0.tag() == ArenaHeaderTag::ReadlineStream
    }

    #[inline]
    pub fn is_stderr(&self) -> bool {
        self.0.tag() == ArenaHeaderTag::StandardErrorStream
    }

    #[inline]
    pub fn is_stdout(&self) -> bool {
        self.0.tag() == ArenaHeaderTag::StandardOutputStream
    }

    #[inline]
    pub fn tag(&self) -> ArenaHeaderTag {
        self.0.tag()
    }

    #[inline]
    pub fn from_owned_string(string: String, arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<ByteStream> = arena_alloc!(
            StreamLayout::new(ByteStream(Cursor::new(string.into_bytes()))),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub fn from_static_string(src: &'static str, arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<StaticStringStream> = arena_alloc!(
            StreamLayout::new(StaticStringStream {
                stream: Cursor::new(src)
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub fn input_channel(channel: Receiver<Vec<u8>>, arena: &mut Arena) -> Self {
        let inner = Cursor::new(Vec::new());
        let ptr: TypedArenaPtr<InputChannelStream> = arena_alloc!(
            StreamLayout::new(InputChannelStream {
                inner,
                eof: false,
                channel
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub fn stdin(arena: &mut Arena, add_history: bool) -> Self {
        #[cfg(unix)]
        use std::io::IsTerminal;
        #[cfg(unix)]
        if !std::io::stdin().is_terminal() {
            use std::os::unix::io::{FromRawFd, RawFd};
            // dup fd 0 so the File can be owned (and closed later) without
            // closing the real stdin.
            let fd = unsafe { libc::dup(0 as RawFd) };
            let file = unsafe { File::from_raw_fd(fd) };

            return Self::from_file_as_input(atom!("user_input"), file, arena);
        }

        let ptr: TypedArenaPtr<ReadlineStream> = arena_alloc!(
            StreamLayout::new(ReadlineStream::new("", add_history)),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub(crate) fn from_file_as_output(
        file_name: Atom,
        file: File,
        is_append: bool,
        arena: &mut Arena,
    ) -> Self {
        let ptr: TypedArenaPtr<OutputFileStream> = arena_alloc!(
            StreamLayout::new(OutputFileStream {
                file_name,
                file,
                is_append
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub(crate) fn from_file_as_input(file_name: Atom, file: File, arena: &mut Arena) -> Stream {
        let ptr: TypedArenaPtr<InputFileStream> = arena_alloc!(
            StreamLayout::new(InputFileStream {
                file_name,
                file: OptInBufReader::new(file),
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub fn stdout(arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<StandardOutputStream> =
            arena_alloc!(StreamLayout::new(StandardOutputStream {}), arena);
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub fn stderr(arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<StandardErrorStream> =
            arena_alloc!(StreamLayout::new(StandardErrorStream {}), arena);
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub fn from_callback(callback: Callback, arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<CallbackStream> = arena_alloc!(
            StreamLayout::new(CallbackStream {
                inner: Cursor::new(Vec::new()),
                callback,
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    pub(crate) fn from_pipe_writer(writer: PipeWriter, arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<PipeWriterStream> =
            arena_alloc!(StreamLayout::new(PipeWriterStream { writer }), arena);
        ptr.into_dynamic_stream()
    }

    pub(crate) fn from_pipe_reader(reader: PipeReader, arena: &mut Arena) -> Self {
        let ptr: TypedArenaPtr<PipeReaderStream> = arena_alloc!(
            StreamLayout::new(OptInBufReader::new(PipeReaderStream { reader })),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[inline]
    pub(crate) fn from_tcp_stream(address: Atom, tcp_stream: TcpStream, arena: &mut Arena) -> Self {
        tcp_stream.set_read_timeout(None).unwrap();
        tcp_stream.set_write_timeout(None).unwrap();

        let ptr: TypedArenaPtr<BufferedNamedTcpStream> = arena_alloc!(
            StreamLayout::new(BufferedNamedTcpStream(OptInBufReader::new(
                NamedTcpStream {
                    address,
                    tcp_stream,
                }
            ))),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[cfg(feature = "tls")]
    #[inline]
    pub(crate) fn from_tls_stream(
        address: Atom,
        tls_stream: TlsStream<Stream>,
        arena: &mut Arena,
    ) -> Self {
        let ptr: TypedArenaPtr<NamedTlsStream> = arena_alloc!(
            StreamLayout::new(OptInBufReader::new(NamedTlsStream {
                address,
                tls_stream
            })),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[cfg(feature = "http")]
    #[inline]
    pub(crate) fn from_http_stream(
        url: Atom,
        http_stream: BytesReader<Bytes>,
        arena: &mut Arena,
    ) -> Self {
        let ptr: TypedArenaPtr<HttpReadStream> = arena_alloc!(
            StreamLayout::new(HttpReadStream {
                url,
                body_reader: OptInBufReader::new(http_stream),
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    #[cfg(feature = "http")]
    #[inline]
    pub(crate) fn from_http_sender(
        response: TypedArenaPtr<HttpResponse>,
        status_code: u16,
        headers: hyper::HeaderMap,
        arena: &mut Arena,
    ) -> Self {
        let ptr: TypedArenaPtr<HttpWriteStream> = arena_alloc!(
            StreamLayout::new(HttpWriteStream {
                response,
                status_code,
                headers: std::mem::ManuallyDrop::new(headers),
                buffer: std::mem::ManuallyDrop::new(Vec::new()),
            }),
            arena
        );
        ptr.into_dynamic_stream()
    }

    pub(crate) fn close(&mut self) -> io::Result<()> {
        self.0.stream.close()?;
        self.0.drop_payload();

        Ok(())
    }

    pub(crate) fn header_ptr(&self) -> *const ArenaHeader {
        self.0.header_loc
    }
}

impl Deref for Stream {
    type Target = StreamLayout<dyn PrologStream>;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl DerefMut for Stream {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.deref_mut()
    }
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
        // cast to *const () to avoid ambiguity of wide pointer comparisons
        self.0
            .as_ptr()
            .cast::<()>()
            .cmp(&other.0.as_ptr().cast::<()>())
    }
}

impl PartialEq for Stream {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::addr_eq(self.0.as_ptr(), other.0.as_ptr())
    }
}

impl Eq for Stream {}

pub(in crate::arena) fn cursor_position<T>(cursor: &Cursor<T>, cursor_len: u64) -> AtEndOfStream {
    match cursor.position().cmp(&cursor_len) {
        Ordering::Equal => AtEndOfStream::At,
        Ordering::Greater => AtEndOfStream::Past,
        Ordering::Less => AtEndOfStream::Not,
    }
}

impl<S: ?Sized + PrologStream> StreamLayout<S> {
    pub(crate) fn reset_layout(&mut self) -> bool {
        self.lines_read = 0;
        self.past_end_of_stream = false;
        self.stream.reset()
    }

    pub(crate) fn position_and_lines_read(&mut self) -> Option<(u64, usize)> {
        // returns lines_read, position.
        self.stream.position().map(|pos| (pos, self.lines_read))
    }

    #[inline]
    pub(crate) fn at_end_of_stream(&mut self) -> bool {
        matches!(self.stream.position_relative_to_end(), AtEndOfStream::At)
    }

    #[inline]
    pub(crate) fn set_layout_position(&mut self, pos: u64) -> io::Result<u64> {
        let pos = self.stream.set_position(pos)?;
        let at_end_of_stream = self.stream.position_relative_to_end();

        if matches!(at_end_of_stream, AtEndOfStream::Past) {
            self.past_end_of_stream = true;
        }

        Ok(pos)
    }
}

impl From<Stream> for HeapCellValue {
    #[inline(always)]
    fn from(stream: Stream) -> Self {
        let header_loc = stream.header_ptr();
        debug_assert!(!header_loc.is_null());
        HeapCellValue::from_arena_header_ptr(header_loc)
    }
}

impl From<Stream> for UntypedArenaPtr {
    fn from(value: Stream) -> Self {
        UntypedArenaPtr::from(value.0)
    }
}
