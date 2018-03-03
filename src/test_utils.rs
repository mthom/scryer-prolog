use prolog::ast::*;
use prolog::heap_print::*;
use prolog::io::*;
use prolog::machine::*;

use std::collections::HashSet;
use std::mem::swap;

pub struct TestOutputter {
    results: Vec<HashSet<String>>,
    contents: HashSet<String>,
    focus: String
}

impl TestOutputter {
    fn cache(&mut self) {
        self.begin_new_var();

        let mut contents = HashSet::new();
        swap(&mut contents, &mut self.contents);
        
        self.results.push(contents);
    }
}

impl HeapCellValueOutputter for TestOutputter {
    type Output = Vec<HashSet<String>>;

    fn new() -> Self {
        TestOutputter { results: vec![],
                        contents: HashSet::new(),
                        focus: String::new() }
    }

    fn append(&mut self, focus: &str) {        
        self.focus += focus;        
    }

    fn begin_new_var(&mut self) {        
        if !self.focus.is_empty() {
            let mut focus = String::new();
            swap(&mut focus, &mut self.focus);
            
            self.contents.insert(focus);
        }
    }

    fn result(self) -> Self::Output {
        self.results
    }

    fn ends_with(&self, s: &str) -> bool {
        self.focus.ends_with(s)
    }

    fn len(&self) -> usize {
        self.focus.len()
    }

    fn truncate(&mut self, len: usize) {
        self.focus.truncate(len);
    }
}

pub fn collect_test_output(wam: &mut Machine, alloc_locs: AllocVarDict, mut heap_locs: HeapVarDict)
                           -> Vec<HashSet<String>>
{
    let mut output = TestOutputter::new();
    
    output = wam.heap_view(&heap_locs, output);
    output.cache();
    
    while let EvalSession::SubsequentQuerySuccess = wam.continue_query(&alloc_locs, &mut heap_locs)
    {
        output = wam.heap_view(&heap_locs, output);
        output.cache();
    }

    output.result()
}

pub fn collect_test_output_with_limit(wam: &mut Machine, alloc_locs: AllocVarDict,
                                      mut heap_locs: HeapVarDict, limit: usize)
                                      -> Vec<HashSet<String>>
{
    let mut output = TestOutputter::new();
    
    output = wam.heap_view(&heap_locs, output);
    output.cache();
    
    let mut count  = 1;

    if count == limit {
        return output.result();
    }

    while let EvalSession::SubsequentQuerySuccess = wam.continue_query(&alloc_locs, &mut heap_locs)
    {
        output = wam.heap_view(&heap_locs, output);
        output.cache();
        
        count += 1;

        if count == limit {
            break;
        }
    }

    output.result()
}

#[allow(dead_code)]
pub fn submit(wam: &mut Machine, buffer: &str) -> bool
{
    wam.reset();
        
    match parse_code(wam, buffer) {
        Ok(tl) =>
            match compile_packet(wam, tl) {
                EvalSession::InitialQuerySuccess(_, _) |
                EvalSession::EntrySuccess |
                EvalSession::SubsequentQuerySuccess =>
                    true,
                _ => false
            },
        Err(e) => panic!("parse error: {:?}", e)
    }
}

#[allow(dead_code)]
pub fn submit_query(wam: &mut Machine, buffer: &str, result: Vec<HashSet<String>>) -> bool
{
    wam.reset();

    match parse_code(wam, buffer) {
        Ok(tl) =>
            match compile_packet(wam, tl) {
                EvalSession::InitialQuerySuccess(alloc_locs, heap_locs) =>
                    result == collect_test_output(wam, alloc_locs, heap_locs),
                EvalSession::EntrySuccess => true,
                _ => false
            },
        Err(e) => panic!("parse error: {:?}", e)
    }
}

#[allow(dead_code)]
pub fn submit_query_with_limit(wam: &mut Machine, buffer: &str,
                               result: Vec<HashSet<String>>, limit: usize)
                               -> bool
{
    wam.reset();

    match parse_code(wam, buffer) {
        Ok(tl) =>
            match compile_packet(wam, tl) {
                EvalSession::InitialQuerySuccess(alloc_locs, heap_locs) =>
                    result == collect_test_output_with_limit(wam, alloc_locs,
                                                             heap_locs, limit),
                EvalSession::EntrySuccess => true,
                _ => false
            },
        Err(e) => panic!("parse error: {:?}", e)
    }
}

#[allow(unused_macros)]
macro_rules! expand_strs {
    ($arr:expr) => (
        $arr.into_iter().map(|s| String::from(*s)).collect()
    )
}

#[allow(unused_macros)]
macro_rules! assert_prolog_success_with_limit {
    ($wam:expr, $buf:expr, [$($res:expr),*], $limit:expr) => (
        assert!(submit_query_with_limit($wam, $buf, vec![$(expand_strs!($res)),*], $limit))
    )
}

#[allow(unused_macros)]
macro_rules! assert_prolog_failure {
    ($wam: expr, $buf: expr) => (
        assert_eq!(submit($wam, $buf), false)
    )
}

#[allow(unused_macros)]
macro_rules! assert_prolog_success {
    ($wam:expr, $query:expr, [$($res:expr),*]) => (
        assert!(submit_query($wam, $query, vec![$(expand_strs!($res)),*]))
    );
    ($wam:expr, $buf:expr) => (
        assert_eq!(submit($wam, $buf), true)
    )
}
