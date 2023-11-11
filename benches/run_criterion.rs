use criterion::{criterion_group, criterion_main, Criterion};

mod setup;

fn bench_criterion(c: &mut Criterion) {
    setup::benches().run_all_criterion(c);
}

criterion_group!(
    name = bench_group;
    config = Criterion::default().sample_size(10);
    targets = bench_criterion
);
criterion_main!(bench_group);
