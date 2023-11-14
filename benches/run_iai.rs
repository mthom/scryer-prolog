use iai_callgrind::{library_benchmark, library_benchmark_group, main};

mod setup;

#[library_benchmark]
#[bench::normal(setup::prolog_benches()["count_edges_short"].setup())]
fn bench_edges(mut run: impl FnMut()) {
    run();
}

#[library_benchmark]
#[bench::normal(setup::prolog_benches()["numlist_short"].setup())]
fn bench_numlist(mut run: impl FnMut()) {
    run();
}

library_benchmark_group!(
    name = bench_group;
    benchmarks = bench_edges, bench_numlist
);
main!(library_benchmark_groups = bench_group);
