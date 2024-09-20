#[cfg(test)]
mod shared_library_tests {
    use std::ffi::{CStr, CString};

    use scryer_prolog::ffi::shared_library::{
        consult_module_string, free_c_string, machine_free, machine_new, query_state_free,
        run_query, run_query_iter, run_query_next,
    };
    use scryer_prolog::machine::Machine;
    use serde_json::{json, Value};

    #[test]
    fn test_scryer_run_multiple_queries_greedy_evaluation() {
        let queries = vec![
            CString::new("true.").unwrap(),
            CString::new("false.").unwrap(),
            CString::new("X=2.").unwrap(),
            CString::new("member(a, [a, b, c]).").unwrap(),
            CString::new(r#"member(A, [a, b, c, "a", "b", "c", f(a), "f(a)", [1, 2, 3]])."#)
                .unwrap(),
        ];

        let expected_results = vec![
            json!({"status": "ok", "result": true}),
            json!({"status": "ok", "result": false}),
            json!({"status": "ok", "result": [{"bindings": {"X":2}}]}),
            json!({"status": "ok", "result": true}),
            json!({"status": "ok", "result": [
            {"bindings": {"A": {"atom": "a"}}},
            {"bindings": {"A": {"atom": "b"}}},
            {"bindings": {"A": {"atom": "c"}}},
            {"bindings": {"A": "a"}},
            {"bindings": {"A": "b"}},
            {"bindings": {"A": "c"}},
            {"bindings": {"A": {"args": [{"atom": "a"}], "functor": "f"}}},
            {"bindings": {"A": "f(a)"}},
            {"bindings": {"A": [1, 2, 3]}}
            ]}),
        ];

        let machine_ptr: *mut Machine = machine_new();
        let module_name = CString::new("tests").unwrap();
        let program = CString::new(":- use_module(library(lists)).").unwrap();
        unsafe {
            consult_module_string(&mut *machine_ptr, module_name.as_ptr(), program.as_ptr());
        }

        for (query, expected) in queries.iter().zip(expected_results.iter()) {
            let result = unsafe { run_query(&mut *machine_ptr, query.as_ptr()) };
            let cstr = unsafe { CStr::from_ptr(result) };
            let output_string = cstr.to_str().unwrap().to_owned();
            let deserialized: Value = serde_json::from_str(&output_string).unwrap();
            assert_eq!(expected, &deserialized);
            unsafe { free_c_string(result) };
        }

        unsafe {
            machine_free(machine_ptr);
        }
    }

    #[test]
    fn test_scryer_run_query_equal_variables() {
        let program =
            CString::new(":- use_module(library(lists)). :- use_module(library(dif)).").unwrap();
        let module_name = CString::new("facts").unwrap();
        let query = CString::new("X=Y.").unwrap();
        let machine_ptr: *mut Machine = machine_new();

        assert!(!machine_ptr.is_null());
        unsafe {
            consult_module_string(&mut *machine_ptr, module_name.as_ptr(), program.as_ptr());
        }
        let query_state = unsafe { run_query_iter(&mut *machine_ptr, query.as_ptr()) };

        let expected_results =
            [r#"{"result":{"bindings": {"X":{"variable": "Y"}}},"status":"ok"}"#];

        let query_state_ref = unsafe { &mut *query_state };
        for expected in &expected_results {
            let result_ptr = run_query_next(&mut *query_state_ref);
            let result_char = unsafe { CStr::from_ptr(result_ptr) };
            let result_s = result_char.to_str().unwrap();
            let result_obj = serde_json::from_str::<serde_json::Value>(result_s).expect("Bad JSON");
            let expected_obj =
                serde_json::from_str::<serde_json::Value>(expected).expect("Bad JSON");
            println!("{result_s:?}");
            assert_eq!(expected_obj, result_obj);
            unsafe {
                free_c_string(result_ptr);
            }
        }

        unsafe { query_state_free(query_state) }
        unsafe {
            machine_free(machine_ptr);
        }
    }

    #[test]
    fn test_scryer_run_query_true_members() {
        let program =
            CString::new(":- use_module(library(lists)). :- use_module(library(dif)).").unwrap();
        let module_name = CString::new("facts").unwrap();
        let query =
            CString::new(r#"member(X, [a,"a",f(a),"f(a)", true, "true", false, "false"])."#)
                .unwrap();
        let machine_ptr: *mut Machine = machine_new();
        unsafe {
            consult_module_string(&mut *machine_ptr, module_name.as_ptr(), program.as_ptr());
        }
        let query_state = unsafe { run_query_iter(&mut *machine_ptr, query.as_ptr()) };

        let expected_results = vec![
            json!({"status": "ok", "result": {"bindings": {"X": {"atom": "a"}}}}),
            json!({"status": "ok", "result": {"bindings": {"X": "a"}}}),
            json!({"status": "ok", "result": {"bindings": {"X": {"args": [{"atom": "a"}], "functor": "f"}}}}),
            json!({"status": "ok", "result": {"bindings": {"X": "f(a)"}}}),
            json!({"status": "ok", "result": {"bindings": {"X": true}}}),
            json!({"status": "ok", "result": {"bindings": {"X": "true"}}}),
            json!({"status": "ok", "result": {"bindings": {"X": false}}}),
            json!({"status": "ok", "result": {"bindings": {"X": "false"}}}),
        ];

        let query_state_ref = unsafe { &mut *query_state };
        for expected in &expected_results {
            let result_ptr = run_query_next(query_state_ref);
            let result_char = unsafe { CStr::from_ptr(result_ptr) };
            let result_s = result_char.to_str().unwrap();
            let result_obj =
                serde_json::from_str::<serde_json::Value>(&result_s).expect("Bad JSON");
            assert_eq!(expected, &result_obj);
            unsafe {
                free_c_string(result_ptr);
            }
        }
    }

    #[test]
    fn test_scryer_run_query_jug_test() {
        let program = CString::new(
            "/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Sparrows over Eagles
   https://www.youtube.com/watch?v=vdabv9EkYrY

   jug(ID,Capacity,Fill) represents a jug

   general pattern:

   moves(StateList) --> [ <MOVE> ],
   { preconditions*, postconditions* },
   <recursive call to moves(UpdatedStateList)>
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- use_module(library(clpz)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).



moves(Js0) --> { member(jug(a,_,1), Js0),
                 member(jug(b,_,1), Js0)}.

moves(Js0) --> [fill(ID)],
        { select(jug(ID, C, _), Js0, Js) },
        moves([jug(ID,C,C)|Js]).

moves(Js0) --> [empty(ID)],
        { select(jug(ID, C, _), Js0, Js) },
        moves([jug(ID,C,0)|Js]).

moves(Js0) --> [from_to(F,T)],
        {
          select(jug(F,FC,FF0), Js0, Js1), % remove jug(F,FC,FF0) from Js0 resulting in Js1
          select(jug(T,TC,TF0), Js1, Js) , % remove jug(T,TC,TF0) from Js1 resulting in Js2
          FF0  #> 0,             % source/from jug shouldn't be empty
          TF0 #< TC,             % target/to jug should not be full
          M #= min(FF0, TC-TF0), % pour it all in (FF0) or top it up (TC-TF0)
          FF #= FF0 - M,         % reflect the water poured out from source jug
          TF #= TF0 + M },       % reflect the water poured into the source jug
        moves([jug(F, FC, FF), jug(T,TC,TF)|Js]).

solve(N, Moves) :- 
         InitialState=moves([jug(a, 5, 2), jug(b,4,1), jug(c, 6, 5), jug(d,2,1),
                            jug(e,3,1)]),
         length(Moves, N), % constrain length of moves to force iterative deepening
         phrase(InitialState, Moves).",
        )
        .unwrap();
        let module_name = CString::new("facts").unwrap();
        let query = CString::new(r#"solve(N, Moves)."#).unwrap();
        let machine_ptr: *mut Machine = machine_new();
        unsafe {
            consult_module_string(&mut *machine_ptr, module_name.as_ptr(), program.as_ptr());
        }
        let query_state = unsafe { run_query_iter(&mut *machine_ptr, query.as_ptr()) };

        let expected_results = [
            r#"{"status": "ok", "result": {"bindings": {"Moves": [{"args": [{"atom": "a"}, {"atom": "c"}], "functor": "from_to"}], "N": 1}}}"#,
        ];

        let query_state_ref = unsafe { &mut *query_state };
        for expected in &expected_results {
            let result_ptr = run_query_next(query_state_ref);
            let result_char = unsafe { CStr::from_ptr(result_ptr) };
            let result_s = result_char.to_str().unwrap();
            let result_obj =
                serde_json::from_str::<serde_json::Value>(&result_s).expect("Bad JSON");
            let expected_obj =
                serde_json::from_str::<serde_json::Value>(&expected).expect("Bad JSON");
            assert_eq!(result_obj, expected_obj);
            unsafe {
                free_c_string(result_ptr);
            }
        }
        unsafe { query_state_free(query_state) }
        unsafe { machine_free(machine_ptr) };
    }

    #[test]
    fn test_scryer_run_query_clpz() {
        let program = CString::new(":- use_module(library(clpz)).").unwrap();
        let module_name = CString::new("facts").unwrap();
        let query = CString::new(r#"X in 1 .. 3."#).unwrap();
        let machine_ptr: *mut Machine = machine_new();
        unsafe {
            consult_module_string(&mut *machine_ptr, module_name.as_ptr(), program.as_ptr());
        }
        let query_state = unsafe { run_query_iter(&mut *machine_ptr, query.as_ptr()) };

        let expected_results =
            [r#"{"status": "ok", "result": {"bindings": {"X": {"variable": "_A"}}}}"#]; // incorrect

        let query_state_ref = unsafe { &mut *query_state };
        for expected in &expected_results {
            let result_ptr = run_query_next(query_state_ref);
            let result_char = unsafe { CStr::from_ptr(result_ptr) };
            let result_s = result_char.to_str().unwrap();
            let result_obj =
                serde_json::from_str::<serde_json::Value>(&result_s).expect("Bad JSON");
            let expected_obj =
                serde_json::from_str::<serde_json::Value>(&expected).expect("Bad JSON");
            assert_eq!(expected_obj, result_obj);
            unsafe {
                free_c_string(result_ptr);
            }
        }
        unsafe { query_state_free(query_state) }
        unsafe { machine_free(machine_ptr) };
    }

    #[test]
    fn test_scryer_run_query_partial_list() {
        let program = CString::new(":- use_module(library(lists)).").unwrap();
        let module_name = CString::new("facts").unwrap();
        let query = CString::new(r#"member(X, [["ab" | "dd"]])."#).unwrap();
        let machine_ptr: *mut Machine = machine_new();
        unsafe {
            consult_module_string(&mut *machine_ptr, module_name.as_ptr(), program.as_ptr());
        }
        let query_state = unsafe { run_query_iter(&mut *machine_ptr, query.as_ptr()) };

        let expected_results = vec![
            json!({"status": "ok", "result": {"bindings": {"X": ["ab", {"atom": "d"}, {"atom": "d"}]}}}),
        ];

        let query_state_ref = unsafe { &mut *query_state };
        for expected in &expected_results {
            let result_ptr = run_query_next(query_state_ref);
            let result_char = unsafe { CStr::from_ptr(result_ptr) };
            let result_s = result_char.to_str().unwrap();
            let result_obj =
                serde_json::from_str::<serde_json::Value>(&result_s).expect("Bad JSON");
            assert_eq!(expected, &result_obj);
            unsafe {
                free_c_string(result_ptr);
            }
        }
    }
}
