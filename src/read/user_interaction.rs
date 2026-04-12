use crossterm::event::{read, Event, KeyEventKind};
pub(crate) use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};
use crossterm::tty::IsTty;

use crate::read::fallback_mode;

pub(crate) fn get_key() -> KeyEvent {
    let key;
    if supported_terminal() {
        enable_raw_mode().expect("failed to enable raw mode");
        loop {
            let key_ = read();
            if let Ok(Event::Key(key_)) = key_ {
                if key_.kind != KeyEventKind::Release {
                    match key_.code {
                        KeyCode::Char(_) | KeyCode::Enter | KeyCode::Tab => {
                            key = key_;
                            break;
                        }
                        _ => (),
                    }
                }
            }
        }
        disable_raw_mode().expect("failed to disable raw mode");
    } else {
        // stdin is not supported terminal type, fallback to limited support mode.
        loop {
            let key_ = fallback_mode::limited_support_read();
            if let Ok(key_) = key_ {
                key = key_;
                break;
            }
        }
    }
    key
}

fn supported_terminal() -> bool {
    // If OS is Windows and stdin is not a tty, it's either a pipe or an unsupported terminal configuration.
    cfg!(not(windows)) || std::io::stdin().is_tty()
}
