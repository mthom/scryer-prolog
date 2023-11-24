# About benches

The `benches` directory contains benchmarks that test scryer-prolog performance.

Benchmarks are run via two harnesses:

* `criterion` - criterion performs statistical analysis of benchmark runs and is
  great for benchmarking locally.
* `iai-callgrind` - this runs the benchmark with callgrind, which is able to
  precisely track the number of instructions executed during the run. This is
  especially helpful in a public CI runner context where neighboring VMs can
  cause a very high wall time variance. While instructions executed is only
  correlated with the desired metric (wall time), this is a good tradeoff for CI
  where that metric is unreliable.

Run benchmarks with the following commands:

```
cargo bench --bench run_criterion

# run a particular criterion benchmark
cargo bench --bench run_criterion -- <benchmark_name>

# run in profiling mode which outputs flamegraphs. Set profile time in seconds:
cargo bench --bench run_criterion -- --profile-time <time>

# to run iai, you need valgrind installed and to install iai-callgrind-runner
# at the same version as is in Cargo.toml:
cargo install iai-callgrind-runner --version 0.7.3

cargo bench --bench run_iai
```

For consistency, both runners -- `run_iai.rs` and `run_criterion.rs` -- import
the same setup code from `setup.rs`.

## Setup

`setup.rs` contains the setup code to run benchmarks. `fn prolog_benches()` at
the top of the file is where the benchmarks are defined.

Benchmarks are organized around running queries against a prolog module file.
Before a benchmark starts, `benchmark.setup()` is called which reads the module
file and initializes a new `scryer_prolog::machine::Machine`.

Each benchmark measurement is done by running a query against the machine. In
the case of criterion each query is run many times, in the case of iai it's run
once.

## Adding benchmarks

This design is meant to suppoort defining lots of benchmarks.

To add a new benchmark:

* Add a new file `benches/[module].pl` that contains setup prolog code. Import
  libraries, define predicates, etc.
* Add a new section in `setup.rs::prolog_benchmarks()` that refers to to the
  file and write a query to be benchmarked.
* If the query mutates the machine, then use `Strategy::Fresh` so the criterion
  benchmark will recreate a new machine for each benchmark run, otherwise use
  `Strategy::Reuse` which has lower overhead. (This is not used by the iai
  benchmark because it only runs once anyway.)

Some tips:

* The goal of benchmarking is to know if a library or engine change improved
  performance or not.
* Once a benchmark is defined and named, avoid changing it's definition. If a
  benchmark needs to change to be more useful, give the new definition a new
  name instead. This will prevent charts from showing wild changes in
  performance just because the definition changed (see previous).
* Aim for queries to execute in less than 0.5s realtime. Longer runtimes make it
  easier for humans to see big differences, but benchmarks either run 10x slower
  (iai) or execute repeatedly to attain statistical significance (criterion) and
  in both cases benchmarking queries that take longer than about 0.5s are
  cumbersome to run.
* Consider that the library runtime actually parses the text output of the top
  level. So don't use custom outputs or it will fail to parse. Also keep the
  output small so it doesn't just benchmark the ouput parsing code.
* DO test the output of the benchmark run, we don't want to count broken
  benchmarks.

## CI

Both benchmark harnesses are run in `.github/workflows/ci.yaml` in the `report`
job, and the results are published as build artifacts.

## Todo

- [ ] Currently, the execution time to load a module is not benchmarked. It
  would be nice to have at least one benchmark for loading a module (probably a
  big one).
- [ ] Write a new action that downloads the test and benchmark results
  artifacts, plots them over time, and publishes a report to github pages.
