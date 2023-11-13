# About benches

The `benches` directory contains benchmarks that test scryer-prolog performance.

Benchmarks are run via two harnesses:

* `iai-callgrind` - this runs the benchmark with callgrind, which is able to
  precisely track the number of instructions executed during the run. This is
  especially helpful in a public CI runner context where neighboring VMs can
  cause a very high wall time variance. This means that it doesn't track wall
  time which is what we really care about, but it is a good tradeoff for CI
  where tracking runtime is unreliable.
* `criterion` - criterion performs statistical analysis of benchmark runs and is
  great for benchmarking locally.

Run them using the following commands:

```
cargo bench --bench run_criterion

# run a particular criterion benchmark
cargo bench --bench run_criterion -- <benchmark_name>

# to run iai, you need valgrind installed and to install iai-callgrind-runner
# at the same version as is in Cargo.toml:
cargo install iai-callgrind-runner --version 0.7.3

cargo bench --bench run_iai
```

For consistency, both runners -- `run_iai.rs` and `run_criterion.rs` -- import
the same setup code from `benches.rs`.

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

* Add a new file `benches/[module].pl` that contains setup code. Import
  libraries, define predicates, etc.
* Add a new section in `setup.rs::benches()` that refers to it and add some
  benchmarks.

Some tips:

* The goal of benchmarking is to know if a library or engine change improved
  performance or not.
* Once a benchmark is defined and named, avoid changing it's definition. In
  general, if a benchmark needs to change to be more useful, give the new
  definition a new name. This will prevent charts from showing wild changes in
  performance just because the definition changed (see previous).
* Aim for queries to execute in less than 0.5s realtime. Longer runtimes make it
  easier for humans to see big differences, but benchmarks either run 10x slower
  (iai) or execute repeatedly to attain statistical significance (criterion) and
  in both cases queries that take longer become cumbersome to run.
* Consider that the library runtime actually parses the text output of the top
  level. So don't use custom outputs or it will fail to parse. Also keep the
  output small so it doesn't just benchmark the ouput parsing code.
* DO test the output of the benchmark run, we don't want to count broken
  benchmarks.
* Because a query may run against the same machine multiple times, don't
  permanently mutate the state of the engine with the query since that will
  taint subsequent runs. (Benchmarking assertz et al is desirable, but will
  require some adjustments to how the machine is set up for runs.)

## CI

Both benchmark harnesses are run in `.github/workflows/ci.yaml` in the `report`
job, and the results are published as build artifacts.

A future action may consume the build artifacts and publish a report using the
results.

## Todo

- [ ] Currently, the execution time to load a module is not benchmarked. It
  would be nice to have at least one benchmark for loading a module (probably a
  big one).
- [ ] Write a new action that consumes the test and benchmark results and plots
  them over time and publishes a report (github pages?).
