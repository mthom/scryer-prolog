use crossterm::event::{KeyCode, KeyEvent, KeyEventKind, KeyEventState, KeyModifiers};
use std::io::{Error, ErrorKind, Read};

// Provide graceful degradation limited support mode if reading from stdin that does not
// support terminal features.
//
// Retrieve a single byte from stdin, does not support full Unicode decoding; only convert
// byte to KeyEvent char if it falls within the ASCII subset of UTF-8.
// Does not support passing through Ctrl-C as a KeyEvent.
//
// We are not supporting multibyte UTF-8 encodings because we are only
// interested in single ASCII characters which are 1-byte UTF-8 characters.
// Multibyte non-ASCII characters would be ignored anyway, so it's not worth the effort.
//
// It is expected that `limited_support_read` will only be used when prompting for user
// input during solution enumeration and the available commands are single ASCII characters.
pub(crate) fn limited_support_read() -> std::io::Result<KeyEvent> {
    #[allow(
        clippy::unbuffered_bytes,
        reason = "We are aware of `bytes()` performance pitfall but don't expect it to be relevant here, we are doing single byte user input I/O."
    )]
    let byte_or_none = std::io::stdin().bytes().next();

    match byte_or_none {
        Some(byte) => match byte {
            Ok(b) => {
                if b.is_ascii() {
                    Ok(map_ascii_to_keyevent(b as char))
                } else {
                    Err(Error::new(ErrorKind::Unsupported, "not supported input"))
                }
            }
            Err(e) => Err(e),
        },
        None => Err(Error::new(ErrorKind::UnexpectedEof, "EOF")),
    }
}

fn map_ascii_to_keyevent(c: char) -> KeyEvent {
    KeyEvent {
        code: KeyCode::Char(c),
        modifiers: KeyModifiers::NONE,
        kind: KeyEventKind::Press,
        state: KeyEventState::empty(),
    }
}
