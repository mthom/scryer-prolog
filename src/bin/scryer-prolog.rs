fn main() -> std::process::ExitCode {
    use std::sync::atomic::Ordering;
    use scryer_prolog::*;

    ctrlc::set_handler(move || {
        scryer_prolog::machine::INTERRUPT.store(true, Ordering::Relaxed);
    }).unwrap();

    let mut wam = machine::Machine::new();
    wam.run_top_level()
}
