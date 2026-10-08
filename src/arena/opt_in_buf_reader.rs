use std::io::{self, BufRead, Cursor, Read};
use std::str;

use bstr::ByteSlice;
use compact_str::*;

const DEFAULT_BUF_SIZE: usize = 8192;

// lazily augment a Read instance with a buffer in situations when a
// buffer is needed for peeking graphemes and reducing the number of
// system calls, e.g. when parsing very large files. "lazy" in the
// sense that buf's value will remain None until explicitly allocated
// by peek_grapheme or fill_buf.
#[derive(Debug)]
pub struct OptInBufReader<S> {
    pub(in crate::arena) reader: S,
    pub(in crate::arena) buf: Option<Cursor<Vec<u8>>>,
}

impl<S> OptInBufReader<S> {
    pub(in crate::arena) fn new(reader: S) -> Self {
        Self { reader, buf: None }
    }

    pub(in crate::arena) fn reader(&self) -> &S {
        &self.reader
    }

    pub(in crate::arena) fn reader_mut(&mut self) -> &S {
        &mut self.reader
    }

    pub(in crate::arena) fn remaining_buf_len(&self) -> usize {
        if let Some(cursor) = &self.buf {
            let pos = cursor.position() as usize;
            cursor.get_ref().len() - pos
        } else {
            0
        }
    }
}

impl<S: Read> Read for OptInBufReader<S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if let Some(cursor) = &mut self.buf {
            cursor.read(buf)
        } else {
            self.reader.read(buf)
        }
    }
}

impl<S: Read> BufRead for OptInBufReader<S> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let cursor = self
            .buf
            .get_or_insert_with(|| Cursor::new(Vec::with_capacity(DEFAULT_BUF_SIZE)));

        if cursor.fill_buf()?.is_empty() {
            let vec = cursor.get_mut();

            match self.reader.read(vec) {
                Ok(0) => {
                    vec.clear();
                    cursor.set_position(0);
                    return Ok(&[]);
                }
                Ok(n) => {
                    vec.truncate(n);
                    cursor.set_position(0);
                }
                Err(e) => {
                    vec.clear();
                    cursor.set_position(0);
                    return Err(e);
                }
            }
        }

        cursor.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        if let Some(ref mut cursor) = self.buf {
            cursor.consume(amt);
        }
    }
}

fn fill_cursor<'a, R: Read>(
    reader: &mut R,
    cursor: &'a mut Cursor<Vec<u8>>,
) -> io::Result<&'a [u8]> {
    let pos = cursor.position() as usize;
    let vec = cursor.get_mut();

    if vec.capacity() == 0 {
        vec.reserve(DEFAULT_BUF_SIZE);
    }

    let old_len = vec.len();
    let cap = vec.capacity();

    if pos >= old_len {
        if old_len < cap {
            vec.resize(cap, 0);
            match reader.read(&mut vec[old_len..cap]) {
                Ok(n) => vec.truncate(old_len + n),
                Err(e) => {
                    vec.truncate(old_len);
                    return Err(e);
                }
            }
        } else {
            let amt = reader.read(&mut vec[0..cap])?;
            vec.truncate(amt);
            cursor.set_position(0);
            return Ok(&cursor.get_ref()[..]);
        }
    }

    Ok(&cursor.get_ref()[pos..])
}

pub(in crate::arena) fn peek_grapheme<'a, R: Read>(
    reader: &mut R,
    at: usize,
    cursor: &'a mut Cursor<Vec<u8>>,
) -> io::Result<Option<&'a str>> {
    if peek_grapheme_impl(reader, at, cursor)? {
        let pos = cursor.position() as usize;
        Ok(cursor
            .get_ref()
            .get(pos + at..)
            .and_then(|slice| slice.graphemes().next()))
    } else {
        Ok(None)
    }
}

// returns true if `g` ends with an unextendable character (like \n,
// \r, or control bytes) under UAX #29 rules, preventing it from
// merging with subsequent bytes
#[inline]
fn is_boundary_safe_grapheme(g: &str) -> bool {
    g.as_bytes().last().map_or(false, |b| b.is_ascii_control())
}

pub(in crate::arena) fn peek_grapheme_impl<R: Read>(
    reader: &mut R,
    at: usize,
    cursor: &mut Cursor<Vec<u8>>,
) -> io::Result<bool> {
    let buf = fill_cursor(reader, cursor)?;

    if buf.is_empty() {
        return Ok(false);
    }

    match buf.get(at..).and_then(|slice| slice.graphemes().next()) {
        Some(g) => {
            if is_boundary_safe_grapheme(g) || at + g.len() < buf.len() {
                Ok(true)
            } else {
                debug_assert_eq!(at + g.len(), buf.len());
                resolve_boundary(reader, at, cursor)?;
                Ok(true)
            }
        }
        None => Ok(false), // EOF
    }
}

fn resolve_boundary<'a, R: Read>(
    reader: &mut R,
    at: usize,
    cursor: &'a mut Cursor<Vec<u8>>,
) -> io::Result<()> {
    let pos = cursor.position() as usize;
    let mut old_len = cursor.get_ref().len() - pos;

    // slide the grapheme beginning at pos to 0.
    cursor.get_mut().copy_within(pos.., 0);
    cursor.set_position(old_len as u64);
    cursor.get_mut().truncate(old_len);

    loop {
        fill_cursor(reader, cursor)?;
        cursor.set_position(0);

        if cursor.get_ref().len() == old_len {
            // EOF: whatever is in scratch is the final grapheme.

            // can't return the first grapheme here without being
            // blocked by the borrow checker, so return () and recover
            // the grapheme up the call stack.
            return Ok(());
        }

        if let Some(mut iter) = cursor.get_ref().get(at..).map(|slice| slice.graphemes()) {
            let first = iter.next();
            let second = iter.next();

            if let (Some(_g1), Some(_g2)) = (first, second) {
                // second grapheme detected, _g1 is now complete.
                return Ok(());
            }
        }

        let cap = cursor.get_ref().capacity();
        old_len = cursor.get_ref().len();

        cursor.get_mut().reserve(2 * cap);
        cursor.set_position(old_len as u64);
    }
}

pub(in crate::arena) fn read_char<R: Read>(reader: &mut R) -> io::Result<Option<char>> {
    let mut buf = [0u8; 4];
    let mut len = 0;

    loop {
        if reader.read(&mut buf[len..len + 1])? == 0 {
            if len == 0 {
                return Ok(None); // EOF
            }
            // bad UTF-8 mid-codepoint!
            return Ok(Some(char::REPLACEMENT_CHARACTER));
        }

        len += 1;

        let (ch, size) = bstr::decode_utf8(&buf[..len]);

        if size > 0 {
            return Ok(Some(ch.unwrap_or(char::REPLACEMENT_CHARACTER)));
        }
    }
}

pub(in crate::arena) fn peek_char<R: Read>(
    reader: &mut R,
    cursor: &mut Cursor<Vec<u8>>,
) -> io::Result<Option<char>> {
    loop {
        let pos = cursor.position() as usize;
        let slice = &cursor.get_ref()[pos..];

        match bstr::decode_utf8(slice) {
            // return Option<char>, amount of bytes read.
            (Some(c), _) => return Ok(Some(c)),
            (None, 0) => {
                // `amt == 0` means `slice` is empty or ends in an incomplete UTF-8 prefix.
                // shift unread bytes to the start of the buffer if necessary.
                if pos > 0 {
                    let unread = slice.len();

                    cursor.get_mut().copy_within(pos.., 0);
                    cursor.get_mut().truncate(unread);
                    cursor.set_position(0);
                }

                if cursor.get_ref().len() >= std::mem::size_of::<char>() {
                    return Ok(Some(char::REPLACEMENT_CHARACTER));
                }

                let mut byte = [0u8; 1];

                if reader.read(&mut byte)? == 0 {
                    // Stream EOF
                    return Ok(if cursor.get_ref().is_empty() {
                        None
                    } else {
                        Some(char::REPLACEMENT_CHARACTER)
                    });
                }

                cursor.get_mut().push(byte[0]);
            }
            (None, amt) => {
                debug_assert!(amt > 0);
                return Ok(Some(char::REPLACEMENT_CHARACTER));
            }
        }
    }
}

pub trait GraphemeRead: Read {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>>;
    // peek the grapheme at the byte offset from current position "at"
    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>>;

    // doesn't e.g. invoke resolve_boundary in OptInBufReader, since
    // UTF-8 codepoints don't prefix each other, which makes it more
    // suitable for IPC streams like TcpStream, PipeReader, etc.
    // peek_grapheme and read_grapheme are meant mainly for use in the
    // parser whose (character) streams use sentinel characters like
    // ".".
    fn read_char(&mut self) -> io::Result<Option<char>>;
    fn peek_char(&mut self) -> io::Result<Option<char>>;
}

impl<R: Read> GraphemeRead for OptInBufReader<R> {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        match self.peek_grapheme(0)?.map(CompactString::new) {
            Some(g) => {
                self.consume(g.len());
                Ok(Some(g))
            }
            None => Ok(None),
        }
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        let cursor = self
            .buf
            .get_or_insert_with(|| Cursor::new(Vec::with_capacity(DEFAULT_BUF_SIZE)));

        peek_grapheme(&mut self.reader, at, cursor)
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        if self.buf.is_none() {
            // if buf isn't already instantiated, don't instantiate it.
            return read_char(&mut self.reader);
        }

        let c = match self.peek_char()? {
            Some(c) => c,
            None => return Ok(None),
        };

        if let Some(cursor) = self.buf.as_mut() {
            let pos = cursor.position() as usize;
            let slice = &cursor.get_ref()[pos..];

            let bytes_to_consume = if c == char::REPLACEMENT_CHARACTER {
                let (_c_opt, amt) = bstr::decode_utf8(slice);
                // if decode_utf8 produced amt 0 from an incomplete
                // sequence at EOF, consume at least 1 byte so we
                // still advance
                amt.max(1)
            } else {
                c.len_utf8()
            };

            cursor.consume(bytes_to_consume);
        }

        Ok(Some(c))
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        // peeking requires buffering. only a scratch buffer is
        // created if a large buffer hasn't been already.
        let cursor = self
            .buf
            .get_or_insert_with(|| Cursor::new(Vec::with_capacity(std::mem::size_of::<char>())));

        peek_char(&mut self.reader, cursor)
    }
}

impl<T: AsRef<[u8]>> GraphemeRead for Cursor<T> {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        match self.peek_grapheme(0)?.map(CompactString::new) {
            Some(g) => {
                self.consume(g.len());
                Ok(Some(g))
            }
            None => Ok(None),
        }
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        let pos = self.position() as usize;
        Ok(self
            .get_ref()
            .as_ref()
            .get(pos + at..)
            .and_then(|slice| slice.as_bytes().graphemes().next()))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        if let Some(c) = self.peek_char()? {
            self.consume(c.len_utf8());
            Ok(Some(c))
        } else {
            Ok(None)
        }
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        let pos = self.position() as usize;
        Ok(self
            .get_ref()
            .as_ref()
            .get(pos..)
            .and_then(|slice| slice.chars().next()))
    }
}

#[cfg(test)]
mod tests {
    use crate::arena::opt_in_buf_reader::*;
    use std::io::Cursor;

    #[test]
    fn plain_string() {
        let mut read_string = Cursor::new("a string");

        for g in "a string".as_bytes().graphemes() {
            assert_eq!(read_string.peek_grapheme(0).unwrap().unwrap(), g);
            assert_eq!(read_string.read_grapheme().unwrap().unwrap(), g);
        }

        assert!(read_string.peek_grapheme(0).unwrap().is_none());
    }

    #[test]
    fn greek_string() {
        let mut read_string = Cursor::new("λέξη");

        for g in "λέξη".as_bytes().graphemes() {
            assert_eq!(read_string.peek_grapheme(0).unwrap().unwrap(), g);
            assert_eq!(read_string.read_grapheme().unwrap().unwrap(), g);
        }

        assert!(read_string.read_grapheme().unwrap().is_none());
    }

    #[test]
    fn russian_string() {
        let mut read_string = Cursor::new("слово");

        for g in "слово".as_bytes().graphemes() {
            assert_eq!(read_string.peek_grapheme(0).unwrap().unwrap(), g);
            assert_eq!(read_string.read_grapheme().unwrap().unwrap(), g);
        }

        assert!(read_string.read_grapheme().unwrap().is_none());
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

        let mut lorem_ipsum_reader = Cursor::new(lorem_ipsum);

        for g in lorem_ipsum.as_bytes().graphemes() {
            assert_eq!(lorem_ipsum_reader.peek_grapheme(0).unwrap().unwrap(), g);
            assert_eq!(lorem_ipsum_reader.read_grapheme().unwrap().unwrap(), g);
        }

        assert!(lorem_ipsum_reader.read_grapheme().unwrap().is_none());
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

        let mut lorem_ipsum_reader = Cursor::new(lorem_ipsum);

        for g in lorem_ipsum.as_bytes().graphemes() {
            assert_eq!(lorem_ipsum_reader.peek_grapheme(0).unwrap().unwrap(), g);
            assert_eq!(lorem_ipsum_reader.read_grapheme().unwrap().unwrap(), g);
        }

        assert!(lorem_ipsum_reader.read_grapheme().unwrap().is_none());
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

        let mut lorem_ipsum_reader = Cursor::new(lorem_ipsum);

        for g in lorem_ipsum.as_bytes().graphemes() {
            assert_eq!(lorem_ipsum_reader.peek_grapheme(0).unwrap().unwrap(), g);
            assert_eq!(lorem_ipsum_reader.read_grapheme().unwrap().unwrap(), g);
        }

        assert!(lorem_ipsum_reader.read_grapheme().unwrap().is_none());
    }
}
