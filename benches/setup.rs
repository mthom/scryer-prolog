use std::{collections::BTreeMap, fs, path::Path};

use criterion::{black_box, Criterion};

use maplit::btreemap;
use scryer_prolog::machine::{
    parsed_results::{QueryMatch, QueryResolution, Value},
    Machine,
};

pub fn benches() -> Benches {
    Benches::new(&[
        (
            "benches/edges.pl", // name of the prolog module file to load
            &[
                (
                    "count_edges_short",                 // name of the benchmark
                    "independent_set_count(ky, Count).", // query to benchmark in the context of the loaded module
                    btreemap! { "Count".to_string() => Value::try_from("2869176".to_string()).unwrap() }, // List of expected bindings
                ),
                (
                    "count_edges", // multiple benchmark queries can be defined per module
                    "independent_set_count(aa, Count).", // consider making the query adjustable to tune the runtime
                    btreemap! { "Count".to_string() => Value::try_from("211954906".to_string()).unwrap(), },
                ),
            ],
        ),
        (
            "benches/numlist.pl",
            &[(
                "numlist_short",
                "run_numlist(1000000, Head).",
                btreemap! { "Head".to_string() => Value::try_from("1".to_string()).unwrap()},
            )],
        ),
    ])
}

pub struct Benches {
    machines: Vec<Machine>,
    runs: BTreeMap<String, Run>,
}

pub struct Run {
    machine_idx: usize,
    name: &'static str,
    query: &'static str,
    bindings: BTreeMap<String, Value>,
}

// Required for using a mutex. It doesn't actually send anything across threads,
// and this is just a benchmark, so it Should Be Fine(tm). ¯\_(ツ)_/¯
unsafe impl Send for Benches {}

impl Benches {
    #[allow(clippy::type_complexity)]
    pub fn new(
        benches: &[(
            &'static str,
            &[(&'static str, &'static str, BTreeMap<String, Value>)],
        )],
    ) -> Self {
        let mut machines = vec![];
        let mut runs = BTreeMap::new();

        for b in benches {
            let content = fs::read_to_string(b.0).unwrap();
            let name = Path::new(b.0).file_stem().unwrap().to_str().unwrap();
            let mut machine = Machine::new_lib();
            machine.load_module_string(name, content);
            machines.push(machine);
            let idx = machines.len() - 1;
            runs.extend(b.1.iter().cloned().map(|r| {
                (
                    r.0.to_string(),
                    Run {
                        machine_idx: idx,
                        name: r.0,
                        query: r.1,
                        bindings: r.2,
                    },
                )
            }));
        }

        Benches { machines, runs }
    }

    #[allow(dead_code)]
    pub fn run_all_criterion(&mut self, c: &mut Criterion) {
        for (_, runner) in self.runs.iter() {
            let machine = &mut self.machines[runner.machine_idx];
            c.bench_function(runner.name, |b| {
                b.iter(|| {
                    Self::run(machine, runner);
                })
            });
        }
    }

    #[allow(dead_code)]
    pub fn run_once(&mut self, name: &str) {
        let runner = &self.runs[name];
        let machine = &mut self.machines[runner.machine_idx];
        Self::run(machine, runner);
    }

    fn run(machine: &mut Machine, runner: &Run) {
        assert_eq!(
            black_box(machine.run_query(black_box(runner.query.to_string()))),
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                runner.bindings.clone()
            )]))
        );
    }
}
