use l2::ast::*;
use std::cell::Cell;
extern crate lalrpop_util as __lalrpop_util;

mod __parse__TopLevel {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports)]

    use l2::ast::*;
    use std::cell::Cell;
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(dead_code)]
    pub enum __Symbol<'input> {
        Term_22_28_22(&'input str),
        Term_22_29_22(&'input str),
        Term_22_2c_22(&'input str),
        Term_22_2e_22(&'input str),
        Term_22_3a_2d_22(&'input str),
        Term_22_3f_2d_22(&'input str),
        Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(&'input str),
        Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(&'input str),
        Termerror(__lalrpop_util::ErrorRecovery<usize, (usize, &'input str), ()>),
        Nt_28_22_2c_22_20_3cTerm_3e_29(Term),
        Nt_28_22_2c_22_20_3cTerm_3e_29_2a(::std::vec::Vec<Term>),
        Nt_28_22_2c_22_20_3cTerm_3e_29_2b(::std::vec::Vec<Term>),
        Nt_28_3cBoxedTerm_3e_20_22_2c_22_29(Box<Term>),
        Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(::std::vec::Vec<Box<Term>>),
        Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(::std::vec::Vec<Box<Term>>),
        NtAtom(Atom),
        NtBoxedTerm(Box<Term>),
        NtClause(Term),
        NtRule(Rule),
        NtTerm(Term),
        NtTopLevel(TopLevel),
        NtVar(Var),
        Nt____TopLevel(TopLevel),
    }
    const __ACTION: &'static [i32] = &[
        // State 0
        0, 0, 0, 0, 0, 8, 9, 10, 0,
        // State 1
        11, 0, 0, -20, 12, 0, 0, 0, 0,
        // State 2
        0, 0, 0, -19, 13, 0, 0, 0, 0,
        // State 3
        0, 0, 0, 14, 0, 0, 0, 0, 0,
        // State 4
        0, 0, 0, 15, 0, 0, 0, 0, 0,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 6
        0, 0, 0, -21, 0, 0, 0, 0, 0,
        // State 7
        0, 0, 0, 0, 0, 0, 9, 19, 0,
        // State 8
        0, 0, 0, -25, 0, 0, 0, 0, 0,
        // State 9
        -11, 0, 0, -11, -11, 0, 0, 0, 0,
        // State 10
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 11
        0, 0, 0, 0, 0, 0, 32, 33, 0,
        // State 12
        0, 0, 0, 0, 0, 0, 32, 33, 0,
        // State 13
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 15
        35, 0, 0, -20, 0, 0, 0, 0, 0,
        // State 16
        0, 0, 0, -19, 0, 0, 0, 0, 0,
        // State 17
        0, 0, 0, 36, 0, 0, 0, 0, 0,
        // State 18
        -11, 0, 0, -11, 0, 0, 0, 0, 0,
        // State 19
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 20
        38, -20, -20, 0, 0, 0, 0, 0, 0,
        // State 21
        0, 39, 40, 0, 0, 0, 0, 0, 0,
        // State 22
        0, -19, -19, 0, 0, 0, 0, 0, 0,
        // State 23
        0, -12, -12, 0, 0, 0, 0, 0, 0,
        // State 24
        0, -21, -21, 0, 0, 0, 0, 0, 0,
        // State 25
        0, -25, -25, 0, 0, 0, 0, 0, 0,
        // State 26
        -11, -11, -11, 0, 0, 0, 0, 0, 0,
        // State 27
        41, 0, -20, -20, 0, 0, 0, 0, 0,
        // State 28
        0, 0, -19, -19, 0, 0, 0, 0, 0,
        // State 29
        0, 0, 43, -17, 0, 0, 0, 0, 0,
        // State 30
        0, 0, -21, -21, 0, 0, 0, 0, 0,
        // State 31
        0, 0, -25, -25, 0, 0, 0, 0, 0,
        // State 32
        -11, 0, -11, -11, 0, 0, 0, 0, 0,
        // State 33
        0, 0, 43, -15, 0, 0, 0, 0, 0,
        // State 34
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 35
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 36
        0, 47, 48, 0, 0, 0, 0, 0, 0,
        // State 37
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 38
        0, 0, 0, -13, -13, 0, 0, 0, 0,
        // State 39
        0, 0, 0, 0, 0, 0, -9, -9, 0,
        // State 40
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 41
        0, 0, 53, -18, 0, 0, 0, 0, 0,
        // State 42
        0, 0, 0, 0, 0, 0, 32, 33, 0,
        // State 43
        0, 0, 53, -16, 0, 0, 0, 0, 0,
        // State 44
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 45
        0, 56, 40, 0, 0, 0, 0, 0, 0,
        // State 46
        0, 0, 0, -14, -14, 0, 0, 0, 0,
        // State 47
        0, 0, 0, 0, 0, 0, -10, -10, 0,
        // State 48
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 49
        0, 58, 40, 0, 0, 0, 0, 0, 0,
        // State 50
        0, 0, 0, 0, 0, 0, 26, 27, 0,
        // State 51
        0, 60, 40, 0, 0, 0, 0, 0, 0,
        // State 52
        0, 0, 0, 0, 0, 0, 32, 33, 0,
        // State 53
        0, 0, -4, -4, 0, 0, 0, 0, 0,
        // State 54
        0, 62, 48, 0, 0, 0, 0, 0, 0,
        // State 55
        0, 0, 0, -13, 0, 0, 0, 0, 0,
        // State 56
        0, 63, 48, 0, 0, 0, 0, 0, 0,
        // State 57
        0, -13, -13, 0, 0, 0, 0, 0, 0,
        // State 58
        0, 64, 48, 0, 0, 0, 0, 0, 0,
        // State 59
        0, 0, -13, -13, 0, 0, 0, 0, 0,
        // State 60
        0, 0, -5, -5, 0, 0, 0, 0, 0,
        // State 61
        0, 0, 0, -14, 0, 0, 0, 0, 0,
        // State 62
        0, -14, -14, 0, 0, 0, 0, 0, 0,
        // State 63
        0, 0, -14, -14, 0, 0, 0, 0, 0,
    ];
    const __EOF_ACTION: &'static [i32] = &[
        0,
        0,
        0,
        0,
        0,
        -26,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        -23,
        -24,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        -22,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    const __GOTO: &'static [i32] = &[
        // State 0
        0, 0, 0, 0, 0, 0, 2, 0, 3, 4, 5, 6, 7, 0,
        // State 1
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 2
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 3
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 4
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 6
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 7
        0, 0, 0, 0, 0, 0, 16, 0, 17, 0, 18, 0, 7, 0,
        // State 8
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 9
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 10
        0, 0, 0, 0, 0, 20, 21, 22, 23, 0, 24, 0, 25, 0,
        // State 11
        0, 0, 0, 0, 0, 0, 28, 0, 29, 0, 30, 0, 31, 0,
        // State 12
        0, 0, 0, 0, 0, 0, 28, 0, 29, 0, 34, 0, 31, 0,
        // State 13
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 15
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 16
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 17
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 18
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 19
        0, 0, 0, 0, 0, 0, 21, 37, 23, 0, 24, 0, 25, 0,
        // State 20
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 21
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 22
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 23
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 24
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 25
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 26
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 27
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 28
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 29
        0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 30
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 31
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 32
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 33
        0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 34
        0, 0, 0, 0, 0, 45, 21, 46, 23, 0, 24, 0, 25, 0,
        // State 35
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 36
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 37
        0, 0, 0, 0, 0, 49, 21, 50, 23, 0, 24, 0, 25, 0,
        // State 38
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 39
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 40
        0, 0, 0, 0, 0, 51, 21, 52, 23, 0, 24, 0, 25, 0,
        // State 41
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 42
        0, 0, 0, 0, 0, 0, 28, 0, 29, 0, 54, 0, 31, 0,
        // State 43
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 44
        0, 0, 0, 0, 0, 0, 21, 55, 23, 0, 24, 0, 25, 0,
        // State 45
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 46
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 47
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 48
        0, 0, 0, 0, 0, 0, 21, 57, 23, 0, 24, 0, 25, 0,
        // State 49
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 50
        0, 0, 0, 0, 0, 0, 21, 59, 23, 0, 24, 0, 25, 0,
        // State 51
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 52
        0, 0, 0, 0, 0, 0, 28, 0, 29, 0, 61, 0, 31, 0,
        // State 53
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 54
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 55
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 56
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 57
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 58
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 59
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 60
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 61
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 62
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 63
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    fn __expected_tokens(__state: usize) -> Vec<::std::string::String> {
        const __TERMINAL: &'static [&'static str] = &[
            r###""(""###,
            r###"")""###,
            r###"",""###,
            r###"".""###,
            r###"":-""###,
            r###""?-""###,
            r###"r#"[A-Z][a-z0-9_]*"#"###,
            r###"r#"[a-z][a-z0-9_]*"#"###,
        ];
        __ACTION[(__state * 9)..].iter().zip(__TERMINAL).filter_map(|(&state, terminal)| {
            if state == 0 {
                None
            } else {
                Some(terminal.to_string())
            }
        }).collect()
    }
    pub fn parse_TopLevel<
        'input,
    >(
        input: &'input str,
    ) -> Result<TopLevel, __lalrpop_util::ParseError<usize, (usize, &'input str), ()>>
    {
        let mut __tokens = super::__intern_token::__Matcher::new(input);
        let mut __states = vec![0_i32];
        let mut __symbols = vec![];
        let mut __integer;
        let mut __lookahead;
        let mut __last_location = Default::default();
        '__shift: loop {
            __lookahead = match __tokens.next() {
                Some(Ok(v)) => v,
                None => break '__shift,
                Some(Err(e)) => return Err(e),
            };
            __last_location = __lookahead.2.clone();
            __integer = match __lookahead.1 {
                (0, _) if true => 0,
                (1, _) if true => 1,
                (2, _) if true => 2,
                (3, _) if true => 3,
                (4, _) if true => 4,
                (5, _) if true => 5,
                (6, _) if true => 6,
                (7, _) if true => 7,
                _ => {
                    let __state = *__states.last().unwrap() as usize;
                    let __error = __lalrpop_util::ParseError::UnrecognizedToken {
                        token: Some(__lookahead),
                        expected: __expected_tokens(__state),
                    };
                    return Err(__error);
                }
            };
            '__inner: loop {
                let __state = *__states.last().unwrap() as usize;
                let __action = __ACTION[__state * 9 + __integer];
                if __action > 0 {
                    let __symbol = match __integer {
                        0 => match __lookahead.1 {
                            (0, __tok0) => __Symbol::Term_22_28_22(__tok0),
                            _ => unreachable!(),
                        },
                        1 => match __lookahead.1 {
                            (1, __tok0) => __Symbol::Term_22_29_22(__tok0),
                            _ => unreachable!(),
                        },
                        2 => match __lookahead.1 {
                            (2, __tok0) => __Symbol::Term_22_2c_22(__tok0),
                            _ => unreachable!(),
                        },
                        3 => match __lookahead.1 {
                            (3, __tok0) => __Symbol::Term_22_2e_22(__tok0),
                            _ => unreachable!(),
                        },
                        4 => match __lookahead.1 {
                            (4, __tok0) => __Symbol::Term_22_3a_2d_22(__tok0),
                            _ => unreachable!(),
                        },
                        5 => match __lookahead.1 {
                            (5, __tok0) => __Symbol::Term_22_3f_2d_22(__tok0),
                            _ => unreachable!(),
                        },
                        6 => match __lookahead.1 {
                            (6, __tok0) => __Symbol::Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(__tok0),
                            _ => unreachable!(),
                        },
                        7 => match __lookahead.1 {
                            (7, __tok0) => __Symbol::Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(__tok0),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    };
                    __states.push(__action - 1);
                    __symbols.push((__lookahead.0, __symbol, __lookahead.2));
                    continue '__shift;
                } else if __action < 0 {
                    if let Some(r) = __reduce(input, __action, Some(&__lookahead.0), &mut __states, &mut __symbols, ::std::marker::PhantomData::<()>) {
                        return r;
                    }
                } else {
                    let __state = *__states.last().unwrap() as usize;
                    let __error = __lalrpop_util::ParseError::UnrecognizedToken {
                        token: Some(__lookahead),
                        expected: __expected_tokens(__state),
                    };
                    return Err(__error)
                }
            }
        }
        loop {
            let __state = *__states.last().unwrap() as usize;
            let __action = __EOF_ACTION[__state];
            if __action < 0 {
                if let Some(r) = __reduce(input, __action, None, &mut __states, &mut __symbols, ::std::marker::PhantomData::<()>) {
                    return r;
                }
            } else {
                let __state = *__states.last().unwrap() as usize;
                let __error = __lalrpop_util::ParseError::UnrecognizedToken {
                    token: None,
                    expected: __expected_tokens(__state),
                };
                return Err(__error);
            }
        }
    }
    pub fn __reduce<
        'input,
    >(
        input: &'input str,
        __action: i32,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i32>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> Option<Result<TopLevel,__lalrpop_util::ParseError<usize, (usize, &'input str), ()>>>
    {
        let __nonterminal = match -__action {
            1 => {
                // ("," <Term>) = ",", Term => ActionFn(15);
                let __sym1 = __pop_NtTerm(__symbols);
                let __sym0 = __pop_Term_22_2c_22(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action15::<>(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29(__nt), __end));
                0
            }
            2 => {
                // ("," <Term>)* =  => ActionFn(13);
                let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
                let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
                let __nt = super::__action13::<>(input, &__start, &__end);
                let __states_len = __states.len();
                __states.truncate(__states_len - 0);
                __symbols.push((__start, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29_2a(__nt), __end));
                1
            }
            3 => {
                // ("," <Term>)* = ("," <Term>)+ => ActionFn(14);
                let __sym0 = __pop_Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action14::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29_2a(__nt), __end));
                1
            }
            4 => {
                // ("," <Term>)+ = ",", Term => ActionFn(23);
                let __sym1 = __pop_NtTerm(__symbols);
                let __sym0 = __pop_Term_22_2c_22(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action23::<>(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__nt), __end));
                2
            }
            5 => {
                // ("," <Term>)+ = ("," <Term>)+, ",", Term => ActionFn(24);
                let __sym2 = __pop_NtTerm(__symbols);
                let __sym1 = __pop_Term_22_2c_22(__symbols);
                let __sym0 = __pop_Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action24::<>(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__nt), __end));
                2
            }
            6 => {
                // (<BoxedTerm> ",") = BoxedTerm, "," => ActionFn(18);
                let __sym1 = __pop_Term_22_2c_22(__symbols);
                let __sym0 = __pop_NtBoxedTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action18::<>(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29(__nt), __end));
                3
            }
            7 => {
                // (<BoxedTerm> ",")* =  => ActionFn(16);
                let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
                let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
                let __nt = super::__action16::<>(input, &__start, &__end);
                let __states_len = __states.len();
                __states.truncate(__states_len - 0);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(__nt), __end));
                4
            }
            8 => {
                // (<BoxedTerm> ",")* = (<BoxedTerm> ",")+ => ActionFn(17);
                let __sym0 = __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action17::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(__nt), __end));
                4
            }
            9 => {
                // (<BoxedTerm> ",")+ = BoxedTerm, "," => ActionFn(29);
                let __sym1 = __pop_Term_22_2c_22(__symbols);
                let __sym0 = __pop_NtBoxedTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action29::<>(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__nt), __end));
                5
            }
            10 => {
                // (<BoxedTerm> ",")+ = (<BoxedTerm> ",")+, BoxedTerm, "," => ActionFn(30);
                let __sym2 = __pop_Term_22_2c_22(__symbols);
                let __sym1 = __pop_NtBoxedTerm(__symbols);
                let __sym0 = __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action30::<>(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__nt), __end));
                5
            }
            11 => {
                // Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(4);
                let __sym0 = __pop_Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action4::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtAtom(__nt), __end));
                6
            }
            12 => {
                // BoxedTerm = Term => ActionFn(5);
                let __sym0 = __pop_NtTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action5::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtBoxedTerm(__nt), __end));
                7
            }
            13 => {
                // Clause = Atom, "(", BoxedTerm, ")" => ActionFn(31);
                let __sym3 = __pop_Term_22_29_22(__symbols);
                let __sym2 = __pop_NtBoxedTerm(__symbols);
                let __sym1 = __pop_Term_22_28_22(__symbols);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym3.2.clone();
                let __nt = super::__action31::<>(input, __sym0, __sym1, __sym2, __sym3);
                let __states_len = __states.len();
                __states.truncate(__states_len - 4);
                __symbols.push((__start, __Symbol::NtClause(__nt), __end));
                8
            }
            14 => {
                // Clause = Atom, "(", (<BoxedTerm> ",")+, BoxedTerm, ")" => ActionFn(32);
                let __sym4 = __pop_Term_22_29_22(__symbols);
                let __sym3 = __pop_NtBoxedTerm(__symbols);
                let __sym2 = __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__symbols);
                let __sym1 = __pop_Term_22_28_22(__symbols);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym4.2.clone();
                let __nt = super::__action32::<>(input, __sym0, __sym1, __sym2, __sym3, __sym4);
                let __states_len = __states.len();
                __states.truncate(__states_len - 5);
                __symbols.push((__start, __Symbol::NtClause(__nt), __end));
                8
            }
            15 => {
                // Rule = Clause, ":-", Term => ActionFn(25);
                let __sym2 = __pop_NtTerm(__symbols);
                let __sym1 = __pop_Term_22_3a_2d_22(__symbols);
                let __sym0 = __pop_NtClause(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action25::<>(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::NtRule(__nt), __end));
                9
            }
            16 => {
                // Rule = Clause, ":-", Term, ("," <Term>)+ => ActionFn(26);
                let __sym3 = __pop_Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__symbols);
                let __sym2 = __pop_NtTerm(__symbols);
                let __sym1 = __pop_Term_22_3a_2d_22(__symbols);
                let __sym0 = __pop_NtClause(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym3.2.clone();
                let __nt = super::__action26::<>(input, __sym0, __sym1, __sym2, __sym3);
                let __states_len = __states.len();
                __states.truncate(__states_len - 4);
                __symbols.push((__start, __Symbol::NtRule(__nt), __end));
                9
            }
            17 => {
                // Rule = Atom, ":-", Term => ActionFn(27);
                let __sym2 = __pop_NtTerm(__symbols);
                let __sym1 = __pop_Term_22_3a_2d_22(__symbols);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action27::<>(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::NtRule(__nt), __end));
                9
            }
            18 => {
                // Rule = Atom, ":-", Term, ("," <Term>)+ => ActionFn(28);
                let __sym3 = __pop_Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__symbols);
                let __sym2 = __pop_NtTerm(__symbols);
                let __sym1 = __pop_Term_22_3a_2d_22(__symbols);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym3.2.clone();
                let __nt = super::__action28::<>(input, __sym0, __sym1, __sym2, __sym3);
                let __states_len = __states.len();
                __states.truncate(__states_len - 4);
                __symbols.push((__start, __Symbol::NtRule(__nt), __end));
                9
            }
            19 => {
                // Term = Clause => ActionFn(9);
                let __sym0 = __pop_NtClause(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action9::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                10
            }
            20 => {
                // Term = Atom => ActionFn(10);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action10::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                10
            }
            21 => {
                // Term = Var => ActionFn(11);
                let __sym0 = __pop_NtVar(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action11::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                10
            }
            22 => {
                // TopLevel = "?-", Term, "." => ActionFn(1);
                let __sym2 = __pop_Term_22_2e_22(__symbols);
                let __sym1 = __pop_NtTerm(__symbols);
                let __sym0 = __pop_Term_22_3f_2d_22(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action1::<>(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::NtTopLevel(__nt), __end));
                11
            }
            23 => {
                // TopLevel = Rule, "." => ActionFn(2);
                let __sym1 = __pop_Term_22_2e_22(__symbols);
                let __sym0 = __pop_NtRule(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action2::<>(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::NtTopLevel(__nt), __end));
                11
            }
            24 => {
                // TopLevel = Term, "." => ActionFn(3);
                let __sym1 = __pop_Term_22_2e_22(__symbols);
                let __sym0 = __pop_NtTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action3::<>(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::NtTopLevel(__nt), __end));
                11
            }
            25 => {
                // Var = r#"[A-Z][a-z0-9_]*"# => ActionFn(12);
                let __sym0 = __pop_Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action12::<>(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtVar(__nt), __end));
                12
            }
            26 => {
                // __TopLevel = TopLevel => ActionFn(0);
                let __sym0 = __pop_NtTopLevel(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action0::<>(input, __sym0);
                return Some(Ok(__nt));
            }
            _ => panic!("invalid action code {}", __action)
        };
        let __state = *__states.last().unwrap() as usize;
        let __next_state = __GOTO[__state * 14 + __nonterminal] - 1;
        __states.push(__next_state);
        None
    }
    fn __pop_Term_22_28_22<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Term_22_28_22(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Term_22_29_22<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Term_22_29_22(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Term_22_2c_22<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Term_22_2c_22(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Term_22_2e_22<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Term_22_2e_22(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Term_22_3a_2d_22<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Term_22_3a_2d_22(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Term_22_3f_2d_22<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Term_22_3f_2d_22(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, &'input str, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Termerror<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, __lalrpop_util::ErrorRecovery<usize, (usize, &'input str), ()>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Termerror(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt_28_22_2c_22_20_3cTerm_3e_29<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Term, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt_28_22_2c_22_20_3cTerm_3e_29_2a<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::vec::Vec<Term>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29_2a(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt_28_22_2c_22_20_3cTerm_3e_29_2b<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::vec::Vec<Term>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt_28_22_2c_22_20_3cTerm_3e_29_2b(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Box<Term>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::vec::Vec<Box<Term>>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, ::std::vec::Vec<Box<Term>>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtAtom<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Atom, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtAtom(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtBoxedTerm<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Box<Term>, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtBoxedTerm(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtClause<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Term, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtClause(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtRule<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Rule, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtRule(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtTerm<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Term, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtTerm(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtTopLevel<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, TopLevel, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtTopLevel(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_NtVar<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, Var, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::NtVar(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
    fn __pop_Nt____TopLevel<
      'input,
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<'input>,usize)>
    ) -> (usize, TopLevel, usize) {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Nt____TopLevel(__v), __r) => (__l, __v, __r),
            _ => panic!("symbol type mismatch")
        }
    }
}
pub use self::__parse__TopLevel::parse_TopLevel;
mod __intern_token {
    extern crate lalrpop_util as __lalrpop_util;
    pub struct __Matcher<'input> {
        text: &'input str,
        consumed: usize,
    }

    fn __tokenize(text: &str) -> Option<(usize, usize)> {
        let mut __chars = text.char_indices();
        let mut __current_match: Option<(usize, usize)> = None;
        let mut __current_state: usize = 0;
        loop {
            match __current_state {
                0 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        40 => /* '(' */ {
                            __current_match = Some((0, __index + 1));
                            __current_state = 1;
                            continue;
                        }
                        41 => /* ')' */ {
                            __current_match = Some((1, __index + 1));
                            __current_state = 2;
                            continue;
                        }
                        44 => /* ',' */ {
                            __current_match = Some((2, __index + 1));
                            __current_state = 3;
                            continue;
                        }
                        46 => /* '.' */ {
                            __current_match = Some((3, __index + 1));
                            __current_state = 4;
                            continue;
                        }
                        58 => /* ':' */ {
                            __current_state = 5;
                            continue;
                        }
                        63 => /* '?' */ {
                            __current_state = 6;
                            continue;
                        }
                        65 ... 90 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 7;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((7, __index + __ch.len_utf8()));
                            __current_state = 8;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                1 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                2 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                3 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                4 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                5 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        45 => /* '-' */ {
                            __current_match = Some((4, __index + 1));
                            __current_state = 10;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                6 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        45 => /* '-' */ {
                            __current_match = Some((5, __index + 1));
                            __current_state = 11;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                7 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        48 ... 57 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 12;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((6, __index + 1));
                            __current_state = 12;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 12;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                8 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        48 ... 57 => {
                            __current_match = Some((7, __index + __ch.len_utf8()));
                            __current_state = 13;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((7, __index + 1));
                            __current_state = 13;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((7, __index + __ch.len_utf8()));
                            __current_state = 13;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                9 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                10 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                11 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        _ => {
                            return __current_match;
                        }
                    }
                }
                12 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        48 ... 57 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 12;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((6, __index + 1));
                            __current_state = 12;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 12;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                13 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        48 ... 57 => {
                            __current_match = Some((7, __index + __ch.len_utf8()));
                            __current_state = 13;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((7, __index + 1));
                            __current_state = 13;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((7, __index + __ch.len_utf8()));
                            __current_state = 13;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                _ => { panic!("invalid state {}", __current_state); }
            }
        }
    }

    impl<'input> __Matcher<'input> {
        pub fn new(s: &'input str) -> __Matcher<'input> {
            __Matcher { text: s, consumed: 0 }
        }
    }

    impl<'input> Iterator for __Matcher<'input> {
        type Item = Result<(usize, (usize, &'input str), usize), __lalrpop_util::ParseError<usize,(usize, &'input str),()>>;

        fn next(&mut self) -> Option<Self::Item> {
            let __text = self.text.trim_left();
            let __whitespace = self.text.len() - __text.len();
            let __start_offset = self.consumed + __whitespace;
            if __text.is_empty() {
                self.text = __text;
                self.consumed = __start_offset;
                None
            } else {
                match __tokenize(__text) {
                    Some((__index, __length)) => {
                        let __result = &__text[..__length];
                        let __remaining = &__text[__length..];
                        let __end_offset = __start_offset + __length;
                        self.text = __remaining;
                        self.consumed = __end_offset;
                        Some(Ok((__start_offset, (__index, __result), __end_offset)))
                    }
                    None => {
                        Some(Err(__lalrpop_util::ParseError::InvalidToken { location: __start_offset }))
                    }
                }
            }
        }
    }
}

#[allow(unused_variables)]
pub fn __action0<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, TopLevel, usize),
) -> TopLevel
{
    (__0)
}

#[allow(unused_variables)]
pub fn __action1<
    'input,
>(
    input: &'input str,
    (_, _, _): (usize, &'input str, usize),
    (_, t, _): (usize, Term, usize),
    (_, _, _): (usize, &'input str, usize),
) -> TopLevel
{
    TopLevel::Query(t)
}

#[allow(unused_variables)]
pub fn __action2<
    'input,
>(
    input: &'input str,
    (_, r, _): (usize, Rule, usize),
    (_, _, _): (usize, &'input str, usize),
) -> TopLevel
{
    TopLevel::Rule(r)
}

#[allow(unused_variables)]
pub fn __action3<
    'input,
>(
    input: &'input str,
    (_, t, _): (usize, Term, usize),
    (_, _, _): (usize, &'input str, usize),
) -> TopLevel
{
    TopLevel::Fact(t)
}

#[allow(unused_variables)]
pub fn __action4<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> Atom
{
    __0.trim().to_string()
}

#[allow(unused_variables)]
pub fn __action5<
    'input,
>(
    input: &'input str,
    (_, t, _): (usize, Term, usize),
) -> Box<Term>
{
    Box::new(t)
}

#[allow(unused_variables)]
pub fn __action6<
    'input,
>(
    input: &'input str,
    (_, a, _): (usize, Atom, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, ts, _): (usize, ::std::vec::Vec<Box<Term>>, usize),
    (_, t, _): (usize, Box<Term>, usize),
    (_, _, _): (usize, &'input str, usize),
) -> Term
{
    {
     	let mut ts = ts;
     	ts.push(t);
	Term::Clause(Cell::new(RegType::Temp(0)), a, ts)
    }
}

#[allow(unused_variables)]
pub fn __action7<
    'input,
>(
    input: &'input str,
    (_, c, _): (usize, Term, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, h, _): (usize, Term, usize),
    (_, cs, _): (usize, ::std::vec::Vec<Term>, usize),
) -> Rule
{
    Rule { head: (c, h), clauses: cs }
}

#[allow(unused_variables)]
pub fn __action8<
    'input,
>(
    input: &'input str,
    (_, a, _): (usize, Atom, usize),
    (_, _, _): (usize, &'input str, usize),
    (_, h, _): (usize, Term, usize),
    (_, cs, _): (usize, ::std::vec::Vec<Term>, usize),
) -> Rule
{
    Rule { head: (Term::Atom(Cell::new(RegType::Temp(0)), a), h),
	        clauses: cs }
}

#[allow(unused_variables)]
pub fn __action9<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Term, usize),
) -> Term
{
    __0
}

#[allow(unused_variables)]
pub fn __action10<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Atom, usize),
) -> Term
{
    Term::Atom(Cell::new(RegType::Temp(0)), __0)
}

#[allow(unused_variables)]
pub fn __action11<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Var, usize),
) -> Term
{
    Term::Var(Cell::new(VarReg::Norm(RegType::Temp(0))), __0)
}

#[allow(unused_variables)]
pub fn __action12<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> Var
{
    __0.trim().to_string()
}

#[allow(unused_variables)]
pub fn __action13<
    'input,
>(
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<Term>
{
    vec![]
}

#[allow(unused_variables)]
pub fn __action14<
    'input,
>(
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Term>, usize),
) -> ::std::vec::Vec<Term>
{
    v
}

#[allow(unused_variables)]
pub fn __action15<
    'input,
>(
    input: &'input str,
    (_, _, _): (usize, &'input str, usize),
    (_, __0, _): (usize, Term, usize),
) -> Term
{
    (__0)
}

#[allow(unused_variables)]
pub fn __action16<
    'input,
>(
    input: &'input str,
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<Box<Term>>
{
    vec![]
}

#[allow(unused_variables)]
pub fn __action17<
    'input,
>(
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Box<Term>>, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    v
}

#[allow(unused_variables)]
pub fn __action18<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Box<Term>, usize),
    (_, _, _): (usize, &'input str, usize),
) -> Box<Term>
{
    (__0)
}

#[allow(unused_variables)]
pub fn __action19<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Box<Term>, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    vec![__0]
}

#[allow(unused_variables)]
pub fn __action20<
    'input,
>(
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Box<Term>>, usize),
    (_, e, _): (usize, Box<Term>, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    { let mut v = v; v.push(e); v }
}

#[allow(unused_variables)]
pub fn __action21<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Term, usize),
) -> ::std::vec::Vec<Term>
{
    vec![__0]
}

#[allow(unused_variables)]
pub fn __action22<
    'input,
>(
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Term>, usize),
    (_, e, _): (usize, Term, usize),
) -> ::std::vec::Vec<Term>
{
    { let mut v = v; v.push(e); v }
}

#[allow(unused_variables)]
pub fn __action23<
    'input,
>(
    input: &'input str,
    __0: (usize, &'input str, usize),
    __1: (usize, Term, usize),
) -> ::std::vec::Vec<Term>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action15(
        input,
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action21(
        input,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action24<
    'input,
>(
    input: &'input str,
    __0: (usize, ::std::vec::Vec<Term>, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, Term, usize),
) -> ::std::vec::Vec<Term>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action15(
        input,
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action22(
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action25<
    'input,
>(
    input: &'input str,
    __0: (usize, Term, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, Term, usize),
) -> Rule
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action13(
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action7(
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action26<
    'input,
>(
    input: &'input str,
    __0: (usize, Term, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, Term, usize),
    __3: (usize, ::std::vec::Vec<Term>, usize),
) -> Rule
{
    let __start0 = __3.0.clone();
    let __end0 = __3.2.clone();
    let __temp0 = __action14(
        input,
        __3,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action7(
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action27<
    'input,
>(
    input: &'input str,
    __0: (usize, Atom, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, Term, usize),
) -> Rule
{
    let __start0 = __2.2.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action13(
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action8(
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action28<
    'input,
>(
    input: &'input str,
    __0: (usize, Atom, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, Term, usize),
    __3: (usize, ::std::vec::Vec<Term>, usize),
) -> Rule
{
    let __start0 = __3.0.clone();
    let __end0 = __3.2.clone();
    let __temp0 = __action14(
        input,
        __3,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action8(
        input,
        __0,
        __1,
        __2,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action29<
    'input,
>(
    input: &'input str,
    __0: (usize, Box<Term>, usize),
    __1: (usize, &'input str, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action18(
        input,
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action19(
        input,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action30<
    'input,
>(
    input: &'input str,
    __0: (usize, ::std::vec::Vec<Box<Term>>, usize),
    __1: (usize, Box<Term>, usize),
    __2: (usize, &'input str, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action18(
        input,
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action20(
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action31<
    'input,
>(
    input: &'input str,
    __0: (usize, Atom, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, Box<Term>, usize),
    __3: (usize, &'input str, usize),
) -> Term
{
    let __start0 = __1.2.clone();
    let __end0 = __2.0.clone();
    let __temp0 = __action16(
        input,
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action6(
        input,
        __0,
        __1,
        __temp0,
        __2,
        __3,
    )
}

#[allow(unused_variables)]
pub fn __action32<
    'input,
>(
    input: &'input str,
    __0: (usize, Atom, usize),
    __1: (usize, &'input str, usize),
    __2: (usize, ::std::vec::Vec<Box<Term>>, usize),
    __3: (usize, Box<Term>, usize),
    __4: (usize, &'input str, usize),
) -> Term
{
    let __start0 = __2.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action17(
        input,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action6(
        input,
        __0,
        __1,
        __temp0,
        __3,
        __4,
    )
}

pub trait __ToTriple<'input, > {
    type Error;
    fn to_triple(value: Self) -> Result<(usize,(usize, &'input str),usize),Self::Error>;
}

impl<'input, > __ToTriple<'input, > for (usize, (usize, &'input str), usize) {
    type Error = ();
    fn to_triple(value: Self) -> Result<(usize,(usize, &'input str),usize),()> {
        Ok(value)
    }
}
impl<'input, > __ToTriple<'input, > for Result<(usize, (usize, &'input str), usize),()> {
    type Error = ();
    fn to_triple(value: Self) -> Result<(usize,(usize, &'input str),usize),()> {
        value
    }
}
