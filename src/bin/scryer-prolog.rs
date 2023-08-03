fn main() {
    use std::sync::atomic::Ordering;
    use scryer_prolog::*;
    use scryer_prolog::atom_table::Atom;

    ctrlc::set_handler(move || {
        scryer_prolog::machine::INTERRUPT.store(true, Ordering::Relaxed);
    }).unwrap();

    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    runtime.block_on(async move {
        let mut wam = machine::Machine::new(Default::default());
        wam.run_top_level(atom!("$toplevel"), (atom!("$repl"), 1));
    });
}
