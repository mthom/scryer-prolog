use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

#[cfg(not(target_os = "windows"))]
use pprof::criterion::{Output, PProfProfiler};

mod setup;

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

criterion_group!(
    name = benches;
    config = config();
    targets = bench_criterion
);
criterion_main!(benches);
