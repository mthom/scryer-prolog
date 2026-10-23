#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
mod setup;

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
mod iai {
    use iai_callgrind::{library_benchmark, library_benchmark_group, main};

    use scryer_prolog::LeafAnswer;

    use super::setup;

    #[library_benchmark]
    #[bench::count_edges(setup::prolog_benches()["count_edges"].setup())]
    #[bench::numlist(setup::prolog_benches()["numlist"].setup())]
    #[bench::csv_codename(setup::prolog_benches()["csv_codename"].setup())]
    #[bench::memberbench_baseline(setup::prolog_benches()["memberbench_baseline"].setup())]
    #[bench::memberbench_if_expanded(setup::prolog_benches()["memberbench_if_expanded"].setup())]
    #[bench::memberbench_if_not_expanded(setup::prolog_benches()["memberbench_if_not_expanded"].setup())]
    fn bench(mut run: impl FnMut() -> Vec<LeafAnswer>) -> Vec<LeafAnswer> {
        run()
    }

    library_benchmark_group!(
        name = benches;
        benchmarks = bench
    );

    main!(library_benchmark_groups = benches);

    pub fn call_main() {
        main()
    }
}

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
fn main() {
    iai::call_main();
}

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
fn main() {}
