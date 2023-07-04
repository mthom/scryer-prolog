/*
 * CharReader is a not entirely redundant flattening/chimera of std's
 * BufReader and unicode_reader's CodePoints, introduced to allow
 * peekable buffered UTF-8 codepoints and access to the underlying
 * reader.
 *
 * Unlike CodePoints, it doesn't make the reader inaccessible by
 * wrapping it a Bytes struct.
 *
 * Unlike BufReader, its buffer is peekable as a char.
 */

use smallvec::*;

use std::error::Error;
use std::fmt;
use std::io;
use std::io::{ErrorKind, IoSliceMut, Read};
use std::str;

pub struct CharReader<R> {
    inner: R,
    buf: SmallVec<[u8;32]>,
    pos: usize,
}

/// An error raised when parsing a UTF-8 byte stream fails.
#[derive(Debug)]
pub struct BadUtf8Error {
    /// The bytes that could not be parsed as a code point.
    pub bytes: Vec<u8>,
}

impl Error for BadUtf8Error {
    fn description(&self) -> &str {
        "BadUtf8Error"
    }
}

impl fmt::Display for BadUtf8Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Bad UTF-8: {:?}", self.bytes)
    }
}

impl<R> CharReader<R> {
    pub fn new(inner: R) -> CharReader<R> {
        Self {
            inner,
            buf: SmallVec::new(),
            pos: 0,
        }
    }

    #[inline]
    pub fn inner(&self) -> &R {
        &self.inner
    }

    #[inline]
    pub fn inner_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    // Return the number of bytes remaining to be read.  Useful for,
    // e.g., determining the position relative to the end of the
    // owning stream.
    #[inline]
    pub fn rem_buf_len(&self) -> usize {
        self.buf.len() - self.pos
    }
}

pub trait CharRead {
    fn read_char(&mut self) -> Option<io::Result<char>> {
        match self.peek_char() {
            Some(Ok(c)) => {
                self.consume(c.len_utf8());
                Some(Ok(c))
            }
            result => result
        }
    }

    fn peek_char(&mut self) -> Option<io::Result<char>>;
    fn put_back_char(&mut self, c: char);
    fn consume(&mut self, nread: usize);
}

impl<R> CharReader<R> {
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    pub fn buffer(&self) -> &[u8] {
        &self.buf[self.pos..]
    }

    pub fn into_inner(self) -> R {
        self.inner
    }

    pub fn reset_buffer(&mut self) {
        self.buf.clear();
        self.pos = 0;
    }
}

impl<R: Read> CharReader<R> {
    pub fn refresh_buffer(&mut self) -> io::Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.
        if self.pos >= self.buf.len() {
            debug_assert!(self.pos == self.buf.len());

            self.buf.clear();

            let mut word = [0u8; std::mem::size_of::<char>()];
            let nread = self.inner.read(&mut word)?;

            self.buf.extend_from_slice(&word[..nread]);
            self.pos = 0;
        }

        Ok(&self.buf[self.pos..])
    }
}

impl<R: Read> CharRead for CharReader<R> {
    fn peek_char(&mut self) -> Option<io::Result<char>> {
        match self.refresh_buffer() {
            Ok(_buf) => {}
            Err(e) => return Some(Err(e)),
        }

        loop {
            let buf = &self.buf[self.pos..];

            if !buf.is_empty() {
                let e = match str::from_utf8(buf) {
                    Ok(s) => {
                        let mut chars = s.chars();
                        let c = chars.next().unwrap();

                        return Some(Ok(c));
                    }
                    Err(e) => {
                        e
                    }
                };

                if buf.len() - e.valid_up_to() >= 4 {
                    // If we have 4 bytes that still don't make up
                    // a valid code point, then we have garbage.

                    // We have bad data in the buffer. Remove
                    // leading bytes until either the buffer is
                    // empty, or we have a valid code point.

                    let mut split_point = 1;
                    let mut badbytes = vec![];

                    loop {
                        let (bad, rest) = buf.split_at(split_point);

                        if rest.is_empty() || str::from_utf8(rest).is_ok() {
                            badbytes.extend_from_slice(bad);
                            break;
                        }

                        split_point += 1;
                    }

                    // Raise the error. If we still have data in
                    // the buffer, it will be returned on the next
                    // loop.

                    return Some(Err(io::Error::new(io::ErrorKind::InvalidData,
                                                   BadUtf8Error { bytes: badbytes })));
                } else {
                    if self.pos >= self.buf.len() {
                        return None;
                    } else if self.buf.len() - self.pos >= 4 {
                        return match str::from_utf8(&self.buf[..e.valid_up_to()]) {
                            Ok(s) => {
                                let mut chars = s.chars();
                                let c = chars.next().unwrap();

                                Some(Ok(c))
                            }
                            Err(e) => {
                                let badbytes = self.buf[..e.valid_up_to()].to_vec();

                                Some(Err(io::Error::new(io::ErrorKind::InvalidData,
                                                        BadUtf8Error { bytes: badbytes })))
                            }
                        };
                    } else {
                        let buf_len = self.buf.len();

                        for (c, idx) in (self.pos..buf_len).enumerate() {
                            self.buf[c] = self.buf[idx];
                        }

                        self.buf.truncate(buf_len - self.pos);

                        let buf_len = self.buf.len();

                        let mut word = [0u8;4];
                        let word_slice = &mut word[buf_len..4];

                        match self.inner.read(word_slice) {
                            Err(e) => return Some(Err(e)),
                            Ok(nread) => {
                                self.buf.extend_from_slice(&word_slice[0..nread]);
                            }
                        }

                        self.pos = 0;
                    }
                }
            } else {
                return None;
            }
        }
    }

    #[inline(always)]
    fn put_back_char(&mut self, c: char) {
        let src_len = self.buf.len() - self.pos;
        debug_assert!(src_len <= self.buf.capacity());

        let c_len = c.len_utf8();
        let mut shifted_slice = [0u8; 32];

        shifted_slice[0..src_len].copy_from_slice(&self.buf[self.pos .. self.buf.len()]);

        self.buf.resize(c_len, 0);
        self.buf.extend_from_slice(&shifted_slice[0..src_len]);
        self.pos = 0;

        c.encode_utf8(&mut self.buf[0..c_len]);
    }

    #[inline(always)]
    fn consume(&mut self, nread: usize) {
        self.pos += nread;
    }
}

impl<R: Read> Read for CharReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // // If we don't have any buffered data and we're doing a massive read
        // // (larger than our internal buffer), bypass our internal buffer
        // // entirely.
        // if self.pos == self.cap && buf.len() >= self.buf.len() {
        //     self.discard_buffer();
        //     return self.inner.read(buf);
        // }

        let mut inner_buf = self.refresh_buffer()?;
        let nread = inner_buf.read(buf)?;

        // let nread = {
        //     let mut rem = self.fill_buf()?;
        //     rem.read(buf)?
        // };

        self.consume(nread);
        Ok(nread)
    }

    // Small read_exacts from a BufReader are extremely common when used with a deserializer.
    // The default implementation calls read in a loop, which results in surprisingly poor code
    // generation for the common path where the buffer has enough bytes to fill the passed-in
    // buffer.
    fn read_exact(&mut self, mut buf: &mut [u8]) -> io::Result<()> {
        if self.buffer().len() >= buf.len() {
            buf.copy_from_slice(&self.buffer()[..buf.len()]);
            self.consume(buf.len());
            return Ok(());
        }

        while !buf.is_empty() {
            match self.read(buf) {
                Ok(0) => break,
                Ok(n) => {
                    let tmp = buf;
                    buf = &mut tmp[n..];
                }
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        if !buf.is_empty() {
            Err(io::Error::new(ErrorKind::UnexpectedEof, "failed to fill whole buffer"))
        } else {
            Ok(())
        }
    }

    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum::<usize>();

        if self.pos == self.buf.len() && total_len >= self.buf.len() {
            self.reset_buffer(); // self.discard_buffer();
            return self.inner.read_vectored(bufs);
        }

        let nread = {
            self.refresh_buffer()?;
            (&self.buf[self.pos..]).read_vectored(bufs)?
        };

        self.consume(nread);
        Ok(nread)
    }
}

/*
#[stable(feature = "rust1", since = "1.0.0")]
impl<R: Read> BufRead for BufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.
        if self.pos >= self.cap {
            debug_assert!(self.pos == self.cap);
            self.cap = self.inner.read(&mut self.buf)?;
            self.pos = 0;
        }
        Ok(&self.buf[self.pos..self.cap])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = cmp::min(self.pos + amt, self.cap);
    }
}
*/

impl<R> fmt::Debug for CharReader<R>
where
    R: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("CharReader")
            .field("reader", &self.inner)
            .field("buf", &format_args!("{}/{}", self.buf.capacity() - self.pos, self.buf.len()))
            .finish()
    }
}


#[cfg(test)]
mod tests {
    use crate::parser::char_reader::*;
    use std::io::Cursor;

    #[test]
    fn plain_string() {
        let mut read_string = CharReader::new(Cursor::new("a string"));

        for c in "a string".chars() {
            assert_eq!(read_string.peek_char().unwrap().ok(), Some(c));
            assert_eq!(read_string.read_char().unwrap().ok(), Some(c));
        }

        assert!(read_string.read_char().is_none());
    }

    #[test]
    fn greek_string() {
        let mut read_string = CharReader::new(Cursor::new("λέξη"));

        for c in "λέξη".chars() {
            assert_eq!(read_string.peek_char().unwrap().ok(), Some(c));
            assert_eq!(read_string.read_char().unwrap().ok(), Some(c));
        }

        assert!(read_string.read_char().is_none());
    }

    #[test]
    fn russian_string() {
        let mut read_string = CharReader::new(Cursor::new("слово"));

        for c in "слово".chars() {
            assert_eq!(read_string.peek_char().unwrap().ok(), Some(c));
            assert_eq!(read_string.read_char().unwrap().ok(), Some(c));
        }

        assert!(read_string.read_char().is_none());
    }

    #[test]
    fn greek_lorem_ipsum() {
        let lorem_ipsum = "Λορεμ ιπσθμ δολορ σιτ αμετ, οφφενδιτ
    εφφιcιενδι σιτ ει, ηαρθμ λεγερε qθαερενδθμ ιθσ νε. Ηασ νο εροσ
    σιγνιφερθμqθε, σεδ ετ μθτατ jθστο, ει cθμ ελιγενδι σcριπτορεμ
    ρεπρεηενδθντ. Εοσ ατ αμετ μαλισ ελειφενδ. Ιν cθμ εριπθιτ
    νομινατι. Θσθ ιν cετεροσ μαιορθμ, μθνερε ατομορθμ ινcιδεριντ θτ
    ηασ. Αν ηασ λιβρισ πραεσεντ πατριοqθε, ηινc θτιναμ πριμισ νε
    cθμ. Cθ μοδο ερρεμ σcριβεντθρ cθμ. Ει vισ δεcορε μαλορθμ
    σεντεντιαε, σεδ νο λιβερ εvερτι μεντιτθμ. Προ φαcερ vολθτπατ
    σαπιεντεμ ιν. Cθ εροσ περσεqθερισ πρι, εα ποσσιτ cετεροσ δθο. Πρι
    εα μαλισ μθνερε.

    Qθισ jθστο μαλορθμ cθ qθο. Νεc ατ οδιο σολετ μαιεστατισ, νε
    φορενσιβθσ σαδιπσcινγ ιθσ, αν qθι ειθσ βρθτε σαπιεντεμ. Cομμθνε
    περcιπιτθρ ιθσ αδ, μθνερε δολορθμ ιμπεδιτ ηισ νε. Νεc ετιαμ
    προπριαε vιτθπερατα ιν. Σονετ νεμορε ιθσ cθ, ιν αφφερτ ινερμισ
    cοτιδιεqθε vισ.

    Ηασ ιδ νονθμυ δοcτθσ cοτιδιεqθε. Σινγθλισ πηιλοσοπηια εξ δθο. Εστ
    νο ιραcθνδια cονσεqθθντθρ. Τε διcτασ επιcθρει εφφιcιαντθρ δθο, εοσ
    νε νθλλα νομιναvι. Εθμ cθ ελιτρ λιβεραvισσε, σιτ περσεqθερισ
    cομπλεcτιτθρ εξ, πονδερθμ σιμιλιqθε ηασ νο.

    Σολθμ ποσσιμ λαβιτθρ εξ ηισ, ει δομινγ εξπετενδισ vελ, διαμ μινιμ
    σcριπσεριτ ει περ. Αθδιαμ οcθρρερετ προ εξ, δομινγ vολθπταρια ετ
    qθο. Cονσθλ σανcτθσ αccθμσαν νο ιθσ, αδ εαμ αλβθcιθσ
    ηονεστατισ. Ετ vιξ φαcιλισ qθαλισqθε ερροριβθσ, ηισ εθ πθρτο
    ασσεντιορ. Ιθσ βονορθμ ηονεστατισ σcριπσεριτ ατ, ιν ναμ εσσε μοvετ
    γραεcο. Αθγθε cονσεcτετθερ εστ ατ.

    Αδ ταλε σθασ μθνερε σεδ, vισ φεθγαιτ αντιοπαμ ιδ. Προ εθ ινερμισ
    σαλθτατθσ, σαεπε qθαεστιο θρβανιτασ cθ περ. Ιν μαλορθμ σαλθτατθσ
    δετερρθισσετ περ, νε παρτεμ vολθτπατ ινστρθcτιορ vιξ. Νο vισ
    δεμοcριτθμ εφφιcιαντθρ, επιcθρει αδολεσcενσ εστ cθ, ιδ vιξ
    λθcιλιθσ αδιπισcινγ. Σεα τε cλιτα ιραcθνδια. Σεα αν σιμθλ
    εσσεντ. Vοcιβθσ ελειφενδ cονσεqθθντθρ περ αδ, αν ναμ πονδερθμ
    vολθπταρια.

    Λιβερ ερθδιτι αccθσαμθσ θτ ναμ. Σιτ αντιοπαμ γθβεργρεν νε. Αμετ
    ανcιλλαε ετ qθι, μεα σολθμ λαθδεμ εα. Εθ μελ παρτεμ οβλιqθε
    πηαεδρθμ. Εξ μελ jθστο αccομμοδαρε, νε νολθισσε σινγθλισ σενσιβθσ
    cθμ, vισ εθ τιμεαμ αδιπισcινγ.

    Τε νολθισσε vολθπτατθμ εστ. Ασσθμ νομιναvι πρι νε, ει νοστρθμ
    επιcθρει μεα. Σεδ cθ ελιτ δεσερθντ, γραεcε ερροριβθσ προ θτ, περ
    νε εθισμοδ vολθπταρια. Νο εθμ διcατ ποσσιμ, νεc πρινcιπεσ
    cονcεπταμ νε. Εθ αππαρεατ ιντελλεγατ σεα. Μελ θτ ελιτ λαθδεμ, θσθ
    δολορεμ cομπλεcτιτθρ ετ, νε μεα δολορεσ μολεστιαε.

    Θσθ λεγενδοσ vολθπτατιβθσ cθ. Qθο νε αδηθc ρεφερρεντθρ, αλια
    μεδιοcρεμ δθο νε, σεδ ερρεμ δολορθμ αccομμοδαρε νε. Ετιαμ εqθιδεμ
    δετερρθισσετ cθ μει, ετ εροσ cετεροσ σεα, εξ vιξ ενιμ cασε
    δετραξιτ. Σεδ σολθτα λιβρισ ειρμοδ τε, νοvθμ ποπθλο νε εθμ. Σθμμο
    αδμοδθμ δεσερθντ εστ εξ, εστ διcαμ εqθιδεμ cθ.

    Ιλλθμ cορπορα ινvιδθντ εαμ ετ. Σεδ μαλισ ταcιματεσ εvερτιτθρ εα,
    μαζιμ νθλλαμ vοcιβθσ μεα ει. Μεα ορνατθσ λθπτατθμ αδιπισcινγ
    αδ. Μεα αφφερτ νοστερ ατ, ναμ αν σολεατ ερροριβθσ. Εξ σεα αεqθε
    μθνερε cετερο, εοσ ηινc ελειφενδ δεμοcριτθμ.";

        let mut lorem_ipsum_reader = CharReader::new(Cursor::new(lorem_ipsum));

        for c in lorem_ipsum.chars() {
            assert_eq!(lorem_ipsum_reader.peek_char().unwrap().ok(), Some(c));
            assert_eq!(lorem_ipsum_reader.read_char().unwrap().ok(), Some(c));
        }

        assert!(lorem_ipsum_reader.read_char().is_none());
    }

    #[test]
    fn armenian_lorem_ipsum() {
        let lorem_ipsum = "լոռեմ իպսում դոլոռ սիթ ամեթ, նովում գռաեծո
        սեա եա, աբհոռռեանթ դիսպութանդո եի քուի. իդ քուոդ ինդոծթում
        եսթ, մեա թե ծոմմոդո ծոռպոռա. եթ ծոնսուլ ադիպիսծինգ ռեֆոռմիդանս
        պեռ, ինեռմիս ֆեուգաիթ նո քուո, թալե սալե պռո եա. եթ նիբհ
        աուգուե վոլումուս դուո, նե ծում եխեռծի սալութաթուս գլոռիաթուռ,
        ծու թաթիոն պռաեսենթ մեդիոծռեմ վիս.

        վիխ եռոս ռեֆեռռենթուռ եու. պեռսիուս վիթուպեռաթոռիբուս ութ սեա,
        վիդե ինվիդունթ պռոբաթուս նո քուո. մեի եռոս մելիուս նոմինավի
        իդ, ութ պռո քուաս քուաեսթիո. եթ նաթում պեթենթիում սուավիթաթե
        հիս. քուի ծոնսթիթութո մեդիոծռիթաթեմ թե. ծեթեռո դեթռածթո
        ծոնծեպթամ սեա եթ. դիսսենթիեթ ելոքուենթիամ թհեոպհռասթուս նեծ
        աթ, աթ ֆածեթե եռիպուիթ վիխ.

        ասսուեվեռիթ սծռիպսեռիթ եսթ եթ, վիդիթ դեբեթ եվեռթի եխ
        եսթ. աութեմ լաուդեմ պոսիդոնիում մեի եի. ռեբում դիծամ ծեթեռոս
        եում ծու. նիհիլ եխպեթենդա ասսուեվեռիթ ուսու ան. ւիսի թաթիոն
        դելենիթ նո իուս, սեդ եխ իդքուե սիգնիֆեռումքուե, բռութե զռիլ
        ալբուծիուս ան պռի.

        մովեթ իռիուռե սալութանդի պեռ նո, եի ոմնիս աֆֆեռթ պեռսեքուեռիս
        իուս, եթ պռաեսենթ մալուիսսեթ եսթ. եսթ պռոբո գուբեռգռեն եթ, հաս
        ին դիամ նումքուամ. ֆեուգաիթ ինվենիռե ռեպուդիանդաե աթ սեդ,
        իուվառեթ ծոնսուլաթու եֆֆիծիանթուռ ուսու եի. ութ մեա ածծումսան
        նոմինավի թինծիդունթ, մեի դիծթա ածծումսան ութ. վիմ ոմնիում
        ելիգենդի սծռիպթոռեմ եու.

        իդ վիս եռռոռ ալիքուիպ ելոքուենթիամ, ադ դելենիթի պեռծիպիթ
        դեֆինիթիոնես իուս. վիմ իուդիծո դեմոծռիթում ծոմպռեհենսամ թե,
        ութ նիհիլ լոբոռթիս վոլուպթաթիբուս վել, դիծունթ մենթիթում
        ֆածիլիսիս եի եում. եսսե սալե մինիմ եոս նե. ագամ ոմնեսքուե ծում
        ին.

        իուվառեթ իուդիծաբիթ ծում աթ, ուսու նիբհ աթքուի դոմինգ եխ. եի
        քուի սանծթուս սենսիբուս, նամ ուբիքուե ապպեթեռե պռոդեսսեթ
        եու. ուսու եթ աուգուե ծոնվենիռե սծռիբենթուռ. ան ոմնիում վեռեառ
        ութռոքուե դուո, եսթ եի լիբեռ մեդիոծռեմ եխպլիծառի, ոմնիս
        աուդիռե թե պռի. վիմ մունեռե սոլեաթ ծու, եռոս ինվենիռե
        դիսպութաթիոնի եի քուո, ան ալթեռա պութենթ լաբոռես պռո. անթիոպամ
        դեմոծռիթում պեռ ին.

        նե քուի ծիբո ելիթռ. նեծ նե լիբեռ վոլուպթուա. նիսլ ծոմմունե
        եխպեթենդիս նամ եխ, իուդիծո պլածեռաթ պեռծիպիթուռ մել նո, եթ
        պառթեմ պութանթ քուի. վիմ թինծիդունթ ածծոմմոդառե աթ, նե նամ
        վիդիթ իռիուռե, պռո եա ելիգենդի պոսթուլանթ ծոնսթիթութո.

        մել ութ ոդիո նուլլամ եխպլիծառի. պռոպռիաե թինծիդունթ
        դելիծաթիսսիմի եամ ան, մոդո քուոդսի ապեռիռի եու եսթ, պեռ աթ
        լաբոռես սենսեռիթ. վիմ ծոնգուե ռեպուդիանդաե եի, նեծ ագամ
        դիծունթ դելիծաթիսսիմի աթ. պոսսիթ լիբեռավիսսե եոս եու.

        աթ ալիա դեբեթ ելաբոռառեթ քուո, ին ալիի ածծումսան ծոնսթիթուամ
        հաս, մել թոթա ոմիթթանթուռ ինսթռուծթիոռ նո. պեռ նե ծաուսաե
        սապիենթեմ, պաուլո ոմնեսքուե եի քուո, եխ ոռաթիո պհիլոսոպհիա
        սիթ. իգնոթա ծաուսաե աթ ուսու, եխ քուո դիծթաս քուոդսի
        ռեպուդիառե. ծոռպոռա պռոդեսսեթ ռեֆեռռենթուռ եոս եխ.

        եու եթիամ ելեիֆենդ մել, սալե սծռիպսեռիթ հիս եու. պոռռո
        ադոլեսծենս մեի եա. ին մեա զռիլ պռոբաթուս սալութաթուս. եոս ադ
        մինիմ թեմպոռիբուս. սեա նե եթիամ.";

        let mut lorem_ipsum_reader = CharReader::new(Cursor::new(lorem_ipsum));

        for c in lorem_ipsum.chars() {
            assert_eq!(lorem_ipsum_reader.peek_char().unwrap().ok(), Some(c));
            assert_eq!(lorem_ipsum_reader.read_char().unwrap().ok(), Some(c));
        }

        assert!(lorem_ipsum_reader.read_char().is_none());
    }

    #[test]
    fn russian_lorem_ipsum() {
        let lorem_ipsum = "Лорем ипсум долор сит амет, атяуи дицам еи
        сит, ид сеа фацилис елаборарет. Меа еу яуас алияуид, те яуи
        саперет аппеллантур. Ех иус диам дицта волуптариа, еу пер
        бруте омиттам аццусата. Хис сапиентем губергрен те, яуидам
        луптатум персеяуерис ад ест.

        Ан алияуип перицулис нам, нец апериам цотидиеяуе волуптатибус
        но. Солум тритани пер ех, меи не одио тритани рецусабо, цу при
        веро мелиоре импердиет. Ин граеци индоцтум салутатус нец, диам
        сцаевола пертинациа про те. Ут сеа дебитис лаборамус
        диссентиас, еи цум яуот лобортис.

        Децоре сингулис вим не. Еос не риденс оффициис, еу нонумы
        лабитур еррорибус хас, вел омнис цонституто посидониум но. Вел
        персиус фастидии репрехендунт ид. Натум иллум ипсум сит ад, еа
        еам новум латине. Еос нолуиссе патриояуе елояуентиам те.

        Стет малис яуаерендум хас ад, прима цотидиеяуе мел ан,
        трацтатос десеруиссе нам ех. Ин малорум сусципиантур вим, ех
        меа граецо тритани адолесценс. Промпта цонцлусионемяуе нам еи,
        дуо ин лаборе алтерум цотидиеяуе. Но елитр промпта сплендиде
        еум, аеяуе ассуеверит цонституам яуи ид. Ад тале еррор
        интеллегебат хас, ерудити граецис хас не, пер ут лабитур
        еуисмод. Те при суммо путант. Про утинам цоммуне урбанитас еа.

        Идяуе репрехендунт еи нам, алии толлит легере нам не, хис еа
        виси адверсариум цонцлусионемяуе. Хас ассум омиттам луцилиус
        ет, вих цонсул малорум фастидии не, сенсибус ассуеверит дуо
        ут. Дуо алиа видит цетеро ат, еа аппареат пертинах вел. Пер
        цонституто инцидеринт ин, убияуе риденс сенсерит цум цу. Про
        ет цетерос темпорибус, те вел пурто суммо, дуо мунере вертерем
        урбанитас ад. Сит оптион елецтрам форенсибус но. Еи татион
        сапиентем ест, лаборе сцрипта сингулис но вим, усу еу елигенди
        персецути.

        Иус ан елецтрам цонтентионес. Меи атяуи нонумес ут, вел амет
        репрехендунт ан, вис еу яуаестио патриояуе. Про синт легере
        детрацто ад. Постеа долорем евертитур при ет, вим номинави
        принципес ирацундиа ех. Доцтус интеллегебат но нам. Фацете
        оффициис нецесситатибус цу меа.

        Промпта симилияуе вис ин. Пер бонорум перицулис аргументум
        ад. Еу дицат фацилис губергрен нам, еффициенди цомпрехенсам
        хас еу. Инани нонумы усу но, ад цонцептам репудиандае
        про. Тота нуллам делицата еа яуо, усу дуис дебет путент еи.

        Вис апериам доценди елояуентиам еа. Ех яуот детрацто
        елояуентиам цум, ерос малис дицерет вис ин. Еа цум модус
        еяуидем, дебет нуллам ан меи. Алтерум омиттам про ет.

        Яуи ех латине алияуам, ан меи одио нуллам. Ид хас омнис ребум
        либрис. Ет убияуе путант дебитис про, ех хис медиоцрем
        партиендо, но елит елецтрам дуо. Еу меа сонет номинави
        цотидиеяуе. Нам фалли новум минимум еу, перфецто ратионибус
        цонституто ад меа.

        Нобис детрацто еам ид, при еу ассум пертинах, те етиам
        проприае салутанди яуо. Легимус сусципиантур ет хас, сед
        поссит дефинитионес еа. Ест не патриояуе омиттантур
        интеллегебат, еу яуо дебет цонцлудатуряуе. Еум ад мнесарчум
        дефинитионем, елитр лаборамус перципитур про не, хас феугаит
        фастидии луцилиус ид. Фастидии интеллегат ех.";

        let mut lorem_ipsum_reader = CharReader::new(Cursor::new(lorem_ipsum));

        for c in lorem_ipsum.chars() {
            assert_eq!(lorem_ipsum_reader.peek_char().unwrap().ok(), Some(c));
            assert_eq!(lorem_ipsum_reader.read_char().unwrap().ok(), Some(c));

            lorem_ipsum_reader.put_back_char(c);

            assert_eq!(lorem_ipsum_reader.peek_char().unwrap().ok(), Some(c));
            assert_eq!(lorem_ipsum_reader.read_char().unwrap().ok(), Some(c));
        }

        assert!(lorem_ipsum_reader.read_char().is_none());
    }
}
