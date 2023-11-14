use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

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

criterion_group!(
    name = bench_group;
    config = Criterion::default().sample_size(10);
    targets = bench_criterion
);
criterion_main!(bench_group);
