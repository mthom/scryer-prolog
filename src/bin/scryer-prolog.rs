fn main() {
    use nix::sys::signal;
    use scryer_prolog::read::readline;
    use scryer_prolog::*;

    let handler = signal::SigHandler::Handler(handle_sigint);
    unsafe { signal::signal(signal::Signal::SIGINT, handler) }.unwrap();

    let mut wam = machine::Machine::new(readline::input_stream(), machine::Stream::stdout());
    wam.run_top_level();
}
