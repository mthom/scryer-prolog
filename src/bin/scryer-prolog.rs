fn main() -> std::process::ExitCode {
    use scryer_prolog::atom_table::Atom;
    use scryer_prolog::*;

    #[cfg(feature = "repl")]
    ctrlc::set_handler(move || {
        scryer_prolog::machine::INTERRUPT.store(true, std::sync::atomic::Ordering::Relaxed);
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
        wam.run_module_predicate(atom!("$toplevel"), (atom!("$repl"), 0))
    })
}
