use crossterm::event::{KeyCode, KeyEvent, KeyEventKind, KeyEventState, KeyModifiers};
use std::io::{Read, Error, ErrorKind};

// Provide graceful degradation limited support mode if reading from stdin that does not 
// support terminal features.
//
// Retrieve a single byte from stdin, does not support full Unicode decoding; only convert 
// byte to KeyEvent char if it falls within the ASCII subset of UTF-8.
//
// Does not support passing through Ctrl-C as a KeyEvent.
pub(crate) fn limited_support_read() -> std::io::Result<KeyEvent> {
    let byte_or_none = std::io::stdin().bytes().next();

    match byte_or_none {
        Some(byte) => match byte {
            Ok(b) => {
                if b.is_ascii() {
                    Ok(map_ascii_to_keyevent(b as char))
                }
                else {
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