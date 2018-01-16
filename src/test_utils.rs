use prolog::codegen::*;
use prolog::fixtures::*;
use prolog::heap_print::*;
use prolog::io::*;
use prolog::machine::*;
use prolog::parser::toplevel::*;

use std::collections::HashSet;

pub struct TestOutputter {
    contents: Vec<String>
}

impl HeapCellValueOutputter for TestOutputter {
    type Output = HashSet<String>;

    fn new() -> Self {
        TestOutputter { contents: vec![] }
    }

    fn append(&mut self, contents: &str) {
        if let Some(ref mut result) = self.contents.last_mut() {
            **result += contents;
        }
    }

    fn begin_new_var(&mut self) {
        self.contents.push(String::new());
    }

    fn result(self) -> Self::Output {
        self.contents.into_iter().collect()
    }

    fn ends_with(&self, s: &str) -> bool {
        if let Some(ref result) = self.contents.last() {
            result.ends_with(s)
        } else {
            false
        }
    }

    fn len(&self) -> usize {
        if let Some(ref result) = self.contents.last() {
            result.len()
        } else {
            0
        }
    }

    fn truncate(&mut self, len: usize) {
        if let Some(ref mut result) = self.contents.last_mut() {
            result.truncate(len);
        }
    }
}

pub fn collect_test_output<'a>(wam: &mut Machine, alloc_locs: AllocVarDict<'a>,
                               mut heap_locs: HeapVarDict<'a>)
                               -> HashSet<String>
{
    let mut output = TestOutputter::new();
    output = wam.heap_view(&heap_locs, output);

    while let EvalSession::SubsequentQuerySuccess = wam.continue_query(&alloc_locs, &mut heap_locs)
    {
        output = wam.heap_view(&heap_locs, output);
    }

    output.result()
}

pub fn collect_test_output_with_limit<'a>(wam: &mut Machine, alloc_locs: AllocVarDict<'a>,
                                          mut heap_locs: HeapVarDict<'a>, limit: usize)
                                          -> HashSet<String>
{
    let mut output = TestOutputter::new();    
    output = wam.heap_view(&heap_locs, output);

    let mut count  = 1;

    if count == limit {
        return output.result();
    }
    
    while let EvalSession::SubsequentQuerySuccess = wam.continue_query(&alloc_locs, &mut heap_locs)
    {        
        output = wam.heap_view(&heap_locs, output);

        count += 1;

        if count == limit {
            break;
        }
    }

    output.result()
}

pub fn submit(wam: &mut Machine, buffer: &str) -> bool
{
    wam.reset();

    match parse_code(buffer.trim(), wam.op_dir()) {
        Ok(tl) =>
            match eval(wam, &tl) {
                EvalSession::InitialQuerySuccess(_, _) |
                EvalSession::EntrySuccess |
                EvalSession::SubsequentQuerySuccess =>
                    true,
                _ => false
            },
        Err(e) => panic!("parse error: {:?}", e)
    }
}

pub fn submit_query(wam: &mut Machine, buffer: &str, result: HashSet<String>) -> bool
{
    wam.reset();

    match parse_code(buffer.trim(), wam.op_dir()) {
        Ok(tl) =>
            match eval(wam, &tl) {
                EvalSession::InitialQuerySuccess(alloc_locs, heap_locs) =>
                    result == collect_test_output(wam, alloc_locs, heap_locs),
                EvalSession::EntrySuccess => true,
                _ => false
            },
        Err(e) => panic!("parse error: {:?}", e)
    }
}

pub fn submit_query_with_limit(wam: &mut Machine, buffer: &str,
                         result: HashSet<String>, limit: usize)
                         -> bool
{
    wam.reset();

    match parse_code(buffer.trim(), wam.op_dir()) {
        Ok(tl) =>
            match eval(wam, &tl) {
                EvalSession::InitialQuerySuccess(alloc_locs, heap_locs) =>
                    result == collect_test_output_with_limit(wam, alloc_locs,
                                                             heap_locs, limit),
                EvalSession::EntrySuccess => true,
                _ => false
            },
        Err(e) => panic!("parse error: {:?}", e)
    }
}

macro_rules! expand_strs {
    ($arr:expr) => (
        $arr.into_iter().map(|s| String::from(*s)).collect()
    )
}

macro_rules! assert_prolog_success_with_limit {
    ($wam:expr, $buf:expr, $res:expr, $limit:expr) => (
        assert!(submit_query_with_limit($wam, $buf, expand_strs!($res), $limit))
    )
}

macro_rules! assert_prolog_failure {
    ($wam: expr, $buf: expr) => (
        assert_eq!(submit($wam, $buf), false)
    )
}

macro_rules! assert_prolog_success {
    ($wam:expr, $query:expr, $res:expr) => (
        assert!(submit_query($wam, $query, expand_strs!($res)))
    );
    ($wam:expr, $buf:expr) => (
        assert_eq!(submit($wam, $buf), true)
    )
}
