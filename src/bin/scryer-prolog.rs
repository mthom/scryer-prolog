fn main() -> std::process::ExitCode {
    use scryer_prolog::*;
    use scryer_prolog::atom_table::Atom;
    use std::sync::atomic::Ordering;

    #[cfg(feature = "repl")]
    ctrlc::set_handler(move || {
        scryer_prolog::machine::INTERRUPT.store(true, Ordering::Relaxed);
    })
    .unwrap();

    #[cfg(target_arch = "wasm32")]
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    #[cfg(not(target_arch = "wasm32"))]
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    runtime.block_on(async move {
        let mut wam = machine::Machine::new(Default::default());
        wam.run_top_level(atom!("$toplevel"), (atom!("$repl"), 1))
    })
}
