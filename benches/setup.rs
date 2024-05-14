use std::{collections::BTreeMap, fs, path::Path};

use maplit::btreemap;
use scryer_prolog::machine::{
    parsed_results::{QueryResolution, Value},
    Machine,
};

pub fn prolog_benches() -> BTreeMap<&'static str, PrologBenchmark> {
    [
        (
            "count_edges",                       // name of the benchmark
            "benches/edges.pl", // name of the prolog module file to load. use the same file in multiple benchmarks
            "independent_set_count(ky, Count).", // query to benchmark in the context of the loaded module. consider making the query adjustable to tune the run time to ~0.1s
            Strategy::Reuse,
            btreemap! { "Count" => Value::Integer(2869176.into()) },
        ),
        (
            "numlist",
            "benches/numlist.pl",
            "run_numlist(1000000, Head).",
            Strategy::Reuse,
            btreemap! { "Head" => Value::Integer(1.into())},
        ),
        (
            "csv_codename",
            "benches/csv.pl",
            "get_codename(\"0020\",Name).",
            Strategy::Reuse,
            btreemap! { "Name" => Value::String("SPACE".into())},
        ),
    ]
    .map(|b| {
        (
            b.0,
            PrologBenchmark {
                name: b.0,
                filename: b.1,
                query: b.2,
                strategy: b.3,
                bindings: b.4,
            },
        )
    })
    .into()
}

pub enum Strategy {
    #[allow(dead_code)]
    Fresh,
    Reuse,
}

#[allow(dead_code)]
pub struct PrologBenchmark {
    pub name: &'static str,
    pub filename: &'static str,
    pub query: &'static str,
    pub strategy: Strategy,
    pub bindings: BTreeMap<&'static str, Value>,
}

impl PrologBenchmark {
    pub fn make_machine(&self) -> Machine {
        let program = fs::read_to_string(self.filename).unwrap();
        let module_name = Path::new(self.filename)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap();
        let mut machine = Machine::new_lib();
        machine.load_module_string(module_name, program);
        machine
    }

    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    pub fn setup(&self) -> impl FnMut() -> QueryResolution {
        let mut machine = self.make_machine();
        let query = self.query;
        move || {
            use criterion::black_box;
            black_box(machine.run_query(black_box(query.to_string()))).unwrap()
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn validate_benchmarks() {
        use super::prolog_benches;
        use scryer_prolog::machine::parsed_results::{QueryMatch, QueryResolution};
        use std::{fmt::Write, fs};

        struct BenchResult {
            pub name: &'static str,
            pub setup_inference_count: u64,
            pub query_inference_count: u64,
        }

        let mut results: Vec<BenchResult> = vec![];

        for (_, r) in prolog_benches() {
            let mut machine = r.make_machine();
            let setup_inference_count = machine.get_inference_count();

            let result = machine.run_query(r.query.to_string()).unwrap();
            let query_inference_count = machine.get_inference_count() - setup_inference_count;

            let expected = QueryResolution::Matches(vec![QueryMatch::from(r.bindings.clone())]);
            assert_eq!(result, expected, "validating benchmark {}", r.name);

            results.push(BenchResult {
                name: r.name,
                setup_inference_count,
                query_inference_count,
            })
        }

        let mut json: String = Default::default();
        json.push('[');
        for r in results {
            json.push('\n');
            write!(
                json,
                r#"{{"name":"{}","setup_inference_count":{},"query_inference_count":{}}},"#,
                r.name, r.setup_inference_count, r.query_inference_count
            )
            .unwrap();
        }
        json.pop(); // trailing comma
        json.push_str("\n]");
        fs::write("target/benchmark_inference_counts.json", json).expect("Unable to write file");
    }
}
