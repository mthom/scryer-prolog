use iai_callgrind::{library_benchmark, library_benchmark_group, main};

mod setup;

#[library_benchmark]
#[bench::normal(setup::benches())]
fn bench_edges(mut b: setup::Benches) {
    b.run_once("count_edges_short");
}

#[library_benchmark]
#[bench::normal(setup::benches())]
fn bench_numlist(mut b: setup::Benches) {
    b.run_once("numlist_short");
}

library_benchmark_group!(
    name = bench_group;
    benchmarks = bench_edges, bench_numlist
);
main!(library_benchmark_groups = bench_group);
