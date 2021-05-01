fn main() {
    use nix::sys::signal;
    use scryer_prolog::read::readline;
    use scryer_prolog::*;

    let handler = signal::SigHandler::Handler(handle_sigint);
    unsafe { signal::signal(signal::Signal::SIGINT, handler) }.unwrap();

    let mut wam = machine::Machine::new(
        readline::input_stream(),
        machine::Stream::stdout(),
        machine::Stream::stderr(),
    );
    wam.run_top_level();
}

pub extern "C" fn handle_sigint(signal: libc::c_int) {
    use nix::sys::signal;
    use std::sync::atomic::Ordering;
    let signal = signal::Signal::from_c_int(signal).unwrap();
    if signal == signal::Signal::SIGINT {
        scryer_prolog::machine::INTERRUPT.store(true, Ordering::Relaxed);
    }
}
