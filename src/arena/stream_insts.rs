use crate::arena::alloc::*;
use crate::arena::opt_in_buf_reader::*;
use crate::atom_table::*;

use bytes::{Bytes, buf::Reader as BytesReader};
use compact_str::CompactString;

use std::error::Error;
use std::fmt::{self, *};
use std::fs::File;
use std::io::{
    self, BufRead, Cursor, ErrorKind, PipeReader, PipeWriter, Read, Seek, SeekFrom, Write,
};
use std::net::*;
use std::sync::mpsc::{Receiver, TryRecvError};

#[cfg(feature = "tls")]
use native_tls::TlsStream;

#[cfg(feature = "http")]
use warp::hyper;

#[cfg(feature = "http")]
use crate::http::HttpResponse;

#[derive(Debug)]
pub enum StreamError {
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

#[derive(Debug)]
pub struct ByteStream(pub(in crate::arena) Cursor<Vec<u8>>);

impl ByteStream {
    #[inline(always)]
    pub fn from_string(string: String) -> Self {
        ByteStream(Cursor::new(string.into()))
    }
}

impl Read for ByteStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}

impl GraphemeRead for ByteStream {
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

impl Write for ByteStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let pos = self.0.position();

        self.0.seek(SeekFrom::End(0))?;
        let result = self.0.write(buf);
        self.0.seek(SeekFrom::Start(pos))?;

        result
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

// for use with the Lexer, which only requires a GraphemeRead
// instance. not a Stream because it bears a non-static lifetime.
#[derive(Debug)]
pub struct BorrowedByteStream<'a>(pub(in crate::arena) Cursor<&'a [u8]>);

impl<'a> BorrowedByteStream<'a> {
    #[inline(always)]
    pub fn from_str(string: &'a str) -> Self {
        BorrowedByteStream(Cursor::new(string.as_bytes()))
    }
}

impl Read for BorrowedByteStream<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}

impl GraphemeRead for BorrowedByteStream<'_> {
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

#[derive(Debug)]
pub struct InputFileStream {
    pub(in crate::arena) file_name: Atom,
    pub(in crate::arena) file: OptInBufReader<File>,
}

impl Read for InputFileStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.file.read(buf)
    }
}

impl GraphemeRead for InputFileStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        self.file.read_grapheme()
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        self.file.peek_grapheme(at)
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        self.file.read_char()
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        self.file.peek_char()
    }
}

impl Write for InputFileStream {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::WriteToInputStream,
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::FlushToInputStream,
        ))
    }
}

#[derive(Debug)]
pub struct OutputFileStream {
    pub(in crate::arena) file_name: Atom,
    pub(in crate::arena) file: File,
    pub(in crate::arena) is_append: bool,
}

impl Read for OutputFileStream {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl GraphemeRead for OutputFileStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_grapheme(&mut self, _at: usize) -> io::Result<Option<&str>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl Write for OutputFileStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.file.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.file.flush()
    }
}

#[derive(Debug)]
pub struct StaticStringStream {
    pub(in crate::arena) stream: Cursor<&'static str>,
}

impl Read for StaticStringStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.stream.read(buf)
    }
}

impl GraphemeRead for StaticStringStream {
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

impl Write for StaticStringStream {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::WriteToInputStream,
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::FlushToInputStream,
        ))
    }
}

#[derive(Debug)]
pub(in crate::arena) struct NamedTcpStream {
    pub(in crate::arena) address: Atom,
    pub(in crate::arena) tcp_stream: TcpStream,
}

impl Read for NamedTcpStream {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.tcp_stream.read(buf)
    }
}

impl Write for OptInBufReader<NamedTcpStream> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.reader.tcp_stream.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.reader.tcp_stream.flush()
    }
}

#[cfg(feature = "tls")]
pub(crate) struct NamedTlsStreamTemplate<S> {
    pub(in crate::arena) address: Atom,
    pub(in crate::arena) tls_stream: TlsStream<S>,
}

impl<S: Read + Write> Read for NamedTlsStreamTemplate<S> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.tls_stream.read(buf)
    }
}

#[cfg(feature = "tls")]
impl<S: Read + Write> Write for OptInBufReader<NamedTlsStreamTemplate<S>> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.reader.tls_stream.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.reader.tls_stream.flush()
    }
}

#[cfg(feature = "http")]
pub struct HttpReadStream {
    pub(in crate::arena) url: Atom,
    pub(in crate::arena) body_reader: OptInBufReader<BytesReader<Bytes>>,
}

#[cfg(feature = "http")]
impl Read for HttpReadStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.body_reader.read(buf)
    }
}

#[cfg(feature = "http")]
impl GraphemeRead for HttpReadStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        self.body_reader.read_grapheme()
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        self.body_reader.peek_grapheme(at)
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        self.body_reader.read_char()
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        self.body_reader.peek_char()
    }
}

#[cfg(feature = "http")]
impl Write for HttpReadStream {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::WriteToInputStream,
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::FlushToInputStream,
        ))
    }
}

#[cfg(feature = "http")]
impl Debug for HttpReadStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Http Read Stream [{}]", self.url.as_str())
    }
}

#[cfg(feature = "http")]
pub struct HttpWriteStream {
    pub(in crate::arena) status_code: u16,
    pub(in crate::arena) headers: std::mem::ManuallyDrop<hyper::HeaderMap>,
    pub(in crate::arena) response: TypedArenaPtr<HttpResponse>,
    pub(in crate::arena) buffer: std::mem::ManuallyDrop<Vec<u8>>,
}

#[cfg(feature = "http")]
impl Read for HttpWriteStream {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl GraphemeRead for HttpWriteStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_grapheme(&mut self, _at: usize) -> io::Result<Option<&str>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

#[cfg(feature = "http")]
impl Write for HttpWriteStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.buffer.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(feature = "http")]
impl Debug for HttpWriteStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Http Write Stream")
    }
}

#[cfg(feature = "http")]
impl Drop for HttpWriteStream {
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
pub struct PipeWriterStream {
    pub(in crate::arena) writer: PipeWriter,
}

impl Read for PipeWriterStream {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl GraphemeRead for PipeWriterStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_grapheme(&mut self, _at: usize) -> io::Result<Option<&str>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl Write for PipeWriterStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.writer.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

#[derive(Debug)]
pub struct StandardOutputStream {}

impl Read for StandardOutputStream {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl GraphemeRead for StandardOutputStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_grapheme(&mut self, _at: usize) -> io::Result<Option<&str>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

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

impl Read for StandardErrorStream {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

impl GraphemeRead for StandardErrorStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_grapheme(&mut self, _at: usize) -> io::Result<Option<&str>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

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
    pub(in crate::arena) inner: Cursor<Vec<u8>>,
    pub(in crate::arena) callback: Callback,
}

impl Read for CallbackStream {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
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

impl Debug for CallbackStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CallbackStream")
            .field("inner", &self.inner)
            .finish()
    }
}

impl GraphemeRead for CallbackStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_grapheme(&mut self, _at: usize) -> io::Result<Option<&str>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::ReadFromOutputStream,
        ))
    }
}

#[derive(Debug)]
pub struct InputChannelStream {
    pub(crate) inner: Cursor<Vec<u8>>,
    pub eof: bool,
    pub(in crate::arena) channel: Receiver<Vec<u8>>,
}

struct ReceiverBifurcatedReader<'a> {
    channel: &'a mut Receiver<Vec<u8>>,
    eof: &'a mut bool,
}

impl Read for ReceiverBifurcatedReader<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self.channel.try_recv() {
            Ok(data) => {
                let amt = data.len().min(buf.len());
                buf[..amt].copy_from_slice(&data[..amt]);
                Ok(amt)
            }
            Err(TryRecvError::Disconnected) => {
                *self.eof = true;
                Ok(0)
            }
            Err(TryRecvError::Empty) => Ok(0),
        }
    }
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

impl GraphemeRead for InputChannelStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        match self.peek_grapheme(0)?.map(CompactString::new) {
            Some(g) => {
                self.inner.consume(g.len());
                Ok(Some(g))
            }
            None => Ok(None),
        }
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        let mut reader = ReceiverBifurcatedReader {
            channel: &mut self.channel,
            eof: &mut self.eof,
        };

        if self.inner.get_ref().is_empty() {
            self.inner = Cursor::new(Vec::with_capacity(256));
        }

        peek_grapheme(&mut reader, at, &mut self.inner)
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        if let Some(c) = self.peek_char()? {
            self.inner.consume(c.len_utf8());
            Ok(Some(c))
        } else {
            Ok(None)
        }
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        let mut reader = ReceiverBifurcatedReader {
            channel: &mut self.channel,
            eof: &mut self.eof,
        };

        if self.inner.get_ref().is_empty() {
            self.inner = Cursor::new(Vec::with_capacity(256));
        }

        peek_char(&mut reader, &mut self.inner)
    }
}

impl Write for InputChannelStream {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::WriteToInputStream,
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::FlushToInputStream,
        ))
    }
}

#[derive(Debug)]
pub struct PipeReaderStream {
    pub(in crate::arena) reader: PipeReader,
}

impl Read for PipeReaderStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let amt = self.reader.read(buf)?;
        Ok(amt)
    }
}

impl Write for OptInBufReader<PipeReaderStream> {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::WriteToInputStream,
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::FlushToInputStream,
        ))
    }
}
