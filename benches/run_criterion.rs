#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
#[cfg(not(target_os = "windows"))]
use pprof::criterion::{Output, PProfProfiler};

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
mod setup;

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
fn bench_criterion(c: &mut Criterion) {
    for (&name, bench) in setup::prolog_benches().iter() {
        match bench.strategy {
            setup::Strategy::Fresh => c.bench_function(name, |b| {
                b.iter_batched(|| bench.setup(), |mut r| r(), BatchSize::LargeInput)
            }),
            setup::Strategy::Reuse => c.bench_function(name, |b| b.iter(bench.setup())),
        };
    }
}
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
#[cfg(not(target_os = "windows"))]
fn config() -> Criterion {
    Criterion::default()
        .sample_size(20)
        .with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)))
}

#[cfg(target_os = "windows")]
fn config() -> Criterion {
    Criterion::default().sample_size(20)
}

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
criterion_group!(
    name = benches;
    config = config();
    targets = bench_criterion
);

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
criterion_main!(benches);

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
fn main() {}
