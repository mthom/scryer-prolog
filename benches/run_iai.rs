#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use iai_callgrind::{library_benchmark, library_benchmark_group, main};
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use scryer_prolog::machine::parsed_results::QueryResolution;

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
mod setup;

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
#[library_benchmark]
#[bench::count_edges(setup::prolog_benches()["count_edges"].setup())]
#[bench::numlist(setup::prolog_benches()["numlist"].setup())]
#[bench::csv_codename(setup::prolog_benches()["csv_codename"].setup())]
fn bench(mut run: impl FnMut() -> QueryResolution) -> QueryResolution {
    run()
}

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
library_benchmark_group!(
    name = benches;
    benchmarks = bench
);
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
main!(library_benchmark_groups = benches);

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
fn main() {}
