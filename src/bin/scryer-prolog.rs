fn main() -> std::process::ExitCode {
    use scryer_prolog::*;
    use std::sync::atomic::Ordering;

    #[cfg(feature = "repl")]
    ctrlc::set_handler(move || {
        scryer_prolog::machine::INTERRUPT.store(true, Ordering::Relaxed);
    })
    .unwrap();

    let mut wam = machine::Machine::new();
    wam.run_top_level()
}
