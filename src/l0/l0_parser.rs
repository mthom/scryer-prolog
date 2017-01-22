use std::cell::{Cell};
use l0::ast::{Atom, Term, TopLevel, Var};
extern crate lalrpop_util as __lalrpop_util;

mod __parse__TopLevel {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports)]

    use std::cell::{Cell};
    use l0::ast::{Atom, Term, TopLevel, Var};
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(dead_code)]
    pub enum __Symbol<'input> {
        Term_22_28_22(&'input str),
        Term_22_29_22(&'input str),
        Term_22_2c_22(&'input str),
        Term_22_2e_22(&'input str),
        Term_22_3f_2d_22(&'input str),
        Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(&'input str),
        Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(&'input str),
        Nt_28_3cBoxedTerm_3e_20_22_2c_22_29(Box<Term>),
        Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(::std::vec::Vec<Box<Term>>),
        Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(::std::vec::Vec<Box<Term>>),
        NtAtom(Atom),
        NtBoxedTerm(Box<Term>),
        NtTerm(Term),
        NtTopLevel(TopLevel),
        NtVar(Var),
        Nt____TopLevel(TopLevel),
    }
    const __ACTION: &'static [i32] = &[
        // State 0
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        6, // on "?-", goto 5
        7, // on r#"[A-Z][a-z0-9_]*"#, goto 6
        8, // on r#"[a-z][a-z0-9_]*"#, goto 7
        // State 1
        9, // on "(", goto 8
        0, // on ")", error
        0, // on ",", error
        -10, // on ".", reduce `Term = Atom => ActionFn(7);`
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 2
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        10, // on ".", goto 9
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 3
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 4
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        -11, // on ".", reduce `Term = Var => ActionFn(8);`
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 5
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        7, // on r#"[A-Z][a-z0-9_]*"#, goto 6
        8, // on r#"[a-z][a-z0-9_]*"#, goto 7
        // State 6
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        -14, // on ".", reduce `Var = r#"[A-Z][a-z0-9_]*"# => ActionFn(4);`
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 7
        -6, // on "(", reduce `Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(3);`
        0, // on ")", error
        0, // on ",", error
        -6, // on ".", reduce `Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(3);`
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 8
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        17, // on r#"[A-Z][a-z0-9_]*"#, goto 16
        18, // on r#"[a-z][a-z0-9_]*"#, goto 17
        // State 9
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 10
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        19, // on ".", goto 18
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 11
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        17, // on r#"[A-Z][a-z0-9_]*"#, goto 16
        18, // on r#"[a-z][a-z0-9_]*"#, goto 17
        // State 12
        21, // on "(", goto 20
        -10, // on ")", reduce `Term = Atom => ActionFn(7);`
        -10, // on ",", reduce `Term = Atom => ActionFn(7);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 13
        0, // on "(", error
        22, // on ")", goto 21
        23, // on ",", goto 22
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 14
        0, // on "(", error
        -7, // on ")", reduce `BoxedTerm = Term => ActionFn(5);`
        -7, // on ",", reduce `BoxedTerm = Term => ActionFn(5);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 15
        0, // on "(", error
        -11, // on ")", reduce `Term = Var => ActionFn(8);`
        -11, // on ",", reduce `Term = Var => ActionFn(8);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 16
        0, // on "(", error
        -14, // on ")", reduce `Var = r#"[A-Z][a-z0-9_]*"# => ActionFn(4);`
        -14, // on ",", reduce `Var = r#"[A-Z][a-z0-9_]*"# => ActionFn(4);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 17
        -6, // on "(", reduce `Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(3);`
        -6, // on ")", reduce `Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(3);`
        -6, // on ",", reduce `Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(3);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 18
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 19
        0, // on "(", error
        24, // on ")", goto 23
        25, // on ",", goto 24
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 20
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        17, // on r#"[A-Z][a-z0-9_]*"#, goto 16
        18, // on r#"[a-z][a-z0-9_]*"#, goto 17
        // State 21
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        -8, // on ".", reduce `Term = Atom, "(", BoxedTerm, ")" => ActionFn(16);`
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 22
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        -4, // on r#"[A-Z][a-z0-9_]*"#, reduce `(<BoxedTerm> ",")+ = BoxedTerm, "," => ActionFn(14);`
        -4, // on r#"[a-z][a-z0-9_]*"#, reduce `(<BoxedTerm> ",")+ = BoxedTerm, "," => ActionFn(14);`
        // State 23
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        -9, // on ".", reduce `Term = Atom, "(", (<BoxedTerm> ",")+, BoxedTerm, ")" => ActionFn(17);`
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 24
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        -5, // on r#"[A-Z][a-z0-9_]*"#, reduce `(<BoxedTerm> ",")+ = (<BoxedTerm> ",")+, BoxedTerm, "," => ActionFn(15);`
        -5, // on r#"[a-z][a-z0-9_]*"#, reduce `(<BoxedTerm> ",")+ = (<BoxedTerm> ",")+, BoxedTerm, "," => ActionFn(15);`
        // State 25
        0, // on "(", error
        0, // on ")", error
        0, // on ",", error
        0, // on ".", error
        0, // on "?-", error
        17, // on r#"[A-Z][a-z0-9_]*"#, goto 16
        18, // on r#"[a-z][a-z0-9_]*"#, goto 17
        // State 26
        0, // on "(", error
        29, // on ")", goto 28
        23, // on ",", goto 22
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 27
        0, // on "(", error
        30, // on ")", goto 29
        25, // on ",", goto 24
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 28
        0, // on "(", error
        -8, // on ")", reduce `Term = Atom, "(", BoxedTerm, ")" => ActionFn(16);`
        -8, // on ",", reduce `Term = Atom, "(", BoxedTerm, ")" => ActionFn(16);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
        // State 29
        0, // on "(", error
        -9, // on ")", reduce `Term = Atom, "(", (<BoxedTerm> ",")+, BoxedTerm, ")" => ActionFn(17);`
        -9, // on ",", reduce `Term = Atom, "(", (<BoxedTerm> ",")+, BoxedTerm, ")" => ActionFn(17);`
        0, // on ".", error
        0, // on "?-", error
        0, // on r#"[A-Z][a-z0-9_]*"#, error
        0, // on r#"[a-z][a-z0-9_]*"#, error
    ];
    const __EOF_ACTION: &'static [i32] = &[
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        -15, // on EOF, reduce `__TopLevel = TopLevel => ActionFn(0);`
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        -13, // on EOF, reduce `TopLevel = Term, "." => ActionFn(2);`
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        -12, // on EOF, reduce `TopLevel = "?-", Term, "." => ActionFn(1);`
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
        0, // on EOF, error
    ];
    const __GOTO: &'static [i32] = &[
        // State 0
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        2, // on Atom, goto 1
        0, // on BoxedTerm, error
        3, // on Term, goto 2
        4, // on TopLevel, goto 3
        5, // on Var, goto 4
        0, // on __TopLevel, error
        // State 1
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 2
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 3
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 4
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 5
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        2, // on Atom, goto 1
        0, // on BoxedTerm, error
        11, // on Term, goto 10
        0, // on TopLevel, error
        5, // on Var, goto 4
        0, // on __TopLevel, error
        // State 6
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 7
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 8
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        12, // on (<BoxedTerm> ",")+, goto 11
        13, // on Atom, goto 12
        14, // on BoxedTerm, goto 13
        15, // on Term, goto 14
        0, // on TopLevel, error
        16, // on Var, goto 15
        0, // on __TopLevel, error
        // State 9
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 10
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 11
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        13, // on Atom, goto 12
        20, // on BoxedTerm, goto 19
        15, // on Term, goto 14
        0, // on TopLevel, error
        16, // on Var, goto 15
        0, // on __TopLevel, error
        // State 12
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 13
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 14
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 15
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 16
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 17
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 18
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 19
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 20
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        26, // on (<BoxedTerm> ",")+, goto 25
        13, // on Atom, goto 12
        27, // on BoxedTerm, goto 26
        15, // on Term, goto 14
        0, // on TopLevel, error
        16, // on Var, goto 15
        0, // on __TopLevel, error
        // State 21
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 22
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 23
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 24
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 25
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        13, // on Atom, goto 12
        28, // on BoxedTerm, goto 27
        15, // on Term, goto 14
        0, // on TopLevel, error
        16, // on Var, goto 15
        0, // on __TopLevel, error
        // State 26
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 27
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 28
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
        // State 29
        0, // on (<BoxedTerm> ","), error
        0, // on (<BoxedTerm> ",")*, error
        0, // on (<BoxedTerm> ",")+, error
        0, // on Atom, error
        0, // on BoxedTerm, error
        0, // on Term, error
        0, // on TopLevel, error
        0, // on Var, error
        0, // on __TopLevel, error
    ];
    pub fn parse_TopLevel<
        'input,
    >(
        input: &'input str,
    ) -> Result<TopLevel, __lalrpop_util::ParseError<usize,(usize, &'input str),()>>
    {
        let mut __tokens = super::__intern_token::__Matcher::new(input);
        let mut __states = vec![0_i32];
        let mut __symbols = vec![];
        '__shift: loop {
            let __lookahead = match __tokens.next() {
                Some(Ok(v)) => v,
                None => break '__shift,
                Some(Err(e)) => return Err(e),
            };
            let __integer = match __lookahead {
                (_, (0, _), _) if true => 0,
                (_, (1, _), _) if true => 1,
                (_, (2, _), _) if true => 2,
                (_, (3, _), _) if true => 3,
                (_, (4, _), _) if true => 4,
                (_, (5, _), _) if true => 5,
                (_, (6, _), _) if true => 6,
                _ => {
                    return Err(__lalrpop_util::ParseError::UnrecognizedToken {
                        token: Some(__lookahead),
                        expected: vec![],
                    });
                }
            };
            loop {
                let __state = *__states.last().unwrap() as usize;
                let __action = __ACTION[__state * 7 + __integer];
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
                            (4, __tok0) => __Symbol::Term_22_3f_2d_22(__tok0),
                            _ => unreachable!(),
                        },
                        5 => match __lookahead.1 {
                            (5, __tok0) => __Symbol::Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(__tok0),
                            _ => unreachable!(),
                        },
                        6 => match __lookahead.1 {
                            (6, __tok0) => __Symbol::Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(__tok0),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    };
                    __states.push(__action - 1);
                    __symbols.push((__lookahead.0, __symbol, __lookahead.2));
                    continue '__shift;
                } else if __action < 0 {
                    if let Some(r) = __reduce(input, __action, Some(&__lookahead.0), &mut __states, &mut __symbols) {
                        return r;
                    }
                } else {
                    return Err(__lalrpop_util::ParseError::UnrecognizedToken {
                        token: Some(__lookahead),
                        expected: vec![],
                    });
                }
            }
        }
        loop {
            let __state = *__states.last().unwrap() as usize;
            let __action = __EOF_ACTION[__state];
            if __action < 0 {
                if let Some(r) = __reduce(input, __action, None, &mut __states, &mut __symbols) {
                    return r;
                }
            } else {
                return Err(__lalrpop_util::ParseError::UnrecognizedToken {
                    token: None,
                    expected: vec![],
                });
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
    ) -> Option<Result<TopLevel,__lalrpop_util::ParseError<usize,(usize, &'input str),()>>>
    {
        let __nonterminal = match -__action {
            1 => {
                // (<BoxedTerm> ",") = BoxedTerm, "," => ActionFn(11);
                let __sym1 = __pop_Term_22_2c_22(__symbols);
                let __sym0 = __pop_NtBoxedTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action11(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29(__nt), __end));
                0
            }
            2 => {
                // (<BoxedTerm> ",")* =  => ActionFn(9);
                let __start = __symbols.last().map(|s| s.2.clone()).unwrap_or_default();
                let __end = __lookahead_start.cloned().unwrap_or_else(|| __start.clone());
                let __nt = super::__action9(input, &__start, &__end);
                let __states_len = __states.len();
                __states.truncate(__states_len - 0);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(__nt), __end));
                1
            }
            3 => {
                // (<BoxedTerm> ",")* = (<BoxedTerm> ",")+ => ActionFn(10);
                let __sym0 = __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action10(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2a(__nt), __end));
                1
            }
            4 => {
                // (<BoxedTerm> ",")+ = BoxedTerm, "," => ActionFn(14);
                let __sym1 = __pop_Term_22_2c_22(__symbols);
                let __sym0 = __pop_NtBoxedTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action14(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__nt), __end));
                2
            }
            5 => {
                // (<BoxedTerm> ",")+ = (<BoxedTerm> ",")+, BoxedTerm, "," => ActionFn(15);
                let __sym2 = __pop_Term_22_2c_22(__symbols);
                let __sym1 = __pop_NtBoxedTerm(__symbols);
                let __sym0 = __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action15(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__nt), __end));
                2
            }
            6 => {
                // Atom = r#"[a-z][a-z0-9_]*"# => ActionFn(3);
                let __sym0 = __pop_Termr_23_22_5ba_2dz_5d_5ba_2dz0_2d9___5d_2a_22_23(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action3(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtAtom(__nt), __end));
                3
            }
            7 => {
                // BoxedTerm = Term => ActionFn(5);
                let __sym0 = __pop_NtTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action5(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtBoxedTerm(__nt), __end));
                4
            }
            8 => {
                // Term = Atom, "(", BoxedTerm, ")" => ActionFn(16);
                let __sym3 = __pop_Term_22_29_22(__symbols);
                let __sym2 = __pop_NtBoxedTerm(__symbols);
                let __sym1 = __pop_Term_22_28_22(__symbols);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym3.2.clone();
                let __nt = super::__action16(input, __sym0, __sym1, __sym2, __sym3);
                let __states_len = __states.len();
                __states.truncate(__states_len - 4);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                5
            }
            9 => {
                // Term = Atom, "(", (<BoxedTerm> ",")+, BoxedTerm, ")" => ActionFn(17);
                let __sym4 = __pop_Term_22_29_22(__symbols);
                let __sym3 = __pop_NtBoxedTerm(__symbols);
                let __sym2 = __pop_Nt_28_3cBoxedTerm_3e_20_22_2c_22_29_2b(__symbols);
                let __sym1 = __pop_Term_22_28_22(__symbols);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym4.2.clone();
                let __nt = super::__action17(input, __sym0, __sym1, __sym2, __sym3, __sym4);
                let __states_len = __states.len();
                __states.truncate(__states_len - 5);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                5
            }
            10 => {
                // Term = Atom => ActionFn(7);
                let __sym0 = __pop_NtAtom(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action7(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                5
            }
            11 => {
                // Term = Var => ActionFn(8);
                let __sym0 = __pop_NtVar(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action8(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtTerm(__nt), __end));
                5
            }
            12 => {
                // TopLevel = "?-", Term, "." => ActionFn(1);
                let __sym2 = __pop_Term_22_2e_22(__symbols);
                let __sym1 = __pop_NtTerm(__symbols);
                let __sym0 = __pop_Term_22_3f_2d_22(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym2.2.clone();
                let __nt = super::__action1(input, __sym0, __sym1, __sym2);
                let __states_len = __states.len();
                __states.truncate(__states_len - 3);
                __symbols.push((__start, __Symbol::NtTopLevel(__nt), __end));
                6
            }
            13 => {
                // TopLevel = Term, "." => ActionFn(2);
                let __sym1 = __pop_Term_22_2e_22(__symbols);
                let __sym0 = __pop_NtTerm(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action2(input, __sym0, __sym1);
                let __states_len = __states.len();
                __states.truncate(__states_len - 2);
                __symbols.push((__start, __Symbol::NtTopLevel(__nt), __end));
                6
            }
            14 => {
                // Var = r#"[A-Z][a-z0-9_]*"# => ActionFn(4);
                let __sym0 = __pop_Termr_23_22_5bA_2dZ_5d_5ba_2dz0_2d9___5d_2a_22_23(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action4(input, __sym0);
                let __states_len = __states.len();
                __states.truncate(__states_len - 1);
                __symbols.push((__start, __Symbol::NtVar(__nt), __end));
                7
            }
            15 => {
                // __TopLevel = TopLevel => ActionFn(0);
                let __sym0 = __pop_NtTopLevel(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action0(input, __sym0);
                return Some(Ok(__nt));
            }
            _ => panic!("invalid action code {}", __action)
        };
        let __state = *__states.last().unwrap() as usize;
        let __next_state = __GOTO[__state * 9 + __nonterminal] - 1;
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
                        63 => /* '?' */ {
                            __current_state = 5;
                            continue;
                        }
                        65 ... 90 => {
                            __current_match = Some((5, __index + __ch.len_utf8()));
                            __current_state = 6;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 7;
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
                            __current_state = 9;
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
                        48 ... 57 => {
                            __current_match = Some((5, __index + __ch.len_utf8()));
                            __current_state = 10;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((5, __index + 1));
                            __current_state = 10;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((5, __index + __ch.len_utf8()));
                            __current_state = 10;
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
                            __current_state = 11;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((6, __index + 1));
                            __current_state = 11;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 11;
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
                        48 ... 57 => {
                            __current_match = Some((5, __index + __ch.len_utf8()));
                            __current_state = 10;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((5, __index + 1));
                            __current_state = 10;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((5, __index + __ch.len_utf8()));
                            __current_state = 10;
                            continue;
                        }
                        _ => {
                            return __current_match;
                        }
                    }
                }
                11 => {
                    let (__index, __ch) = match __chars.next() { Some(p) => p, None => return __current_match };
                    match __ch as u32 {
                        48 ... 57 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 11;
                            continue;
                        }
                        95 => /* '_' */ {
                            __current_match = Some((6, __index + 1));
                            __current_state = 11;
                            continue;
                        }
                        97 ... 122 => {
                            __current_match = Some((6, __index + __ch.len_utf8()));
                            __current_state = 11;
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
    (_, t, _): (usize, Term, usize),
    (_, _, _): (usize, &'input str, usize),
) -> TopLevel
{
    TopLevel::Fact(t)
}

#[allow(unused_variables)]
pub fn __action3<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> Atom
{
    __0.trim().to_string()
}

#[allow(unused_variables)]
pub fn __action4<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, &'input str, usize),
) -> Var
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
	      Term::Clause(Cell::new(0), a, ts)
     }
}

#[allow(unused_variables)]
pub fn __action7<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Atom, usize),
) -> Term
{
    Term::Atom(Cell::new(0), __0)
}

#[allow(unused_variables)]
pub fn __action8<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Var, usize),
) -> Term
{
    Term::Var(Cell::new(0), __0)
}

#[allow(unused_variables)]
pub fn __action9<
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
pub fn __action10<
    'input,
>(
    input: &'input str,
    (_, v, _): (usize, ::std::vec::Vec<Box<Term>>, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    v
}

#[allow(unused_variables)]
pub fn __action11<
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
pub fn __action12<
    'input,
>(
    input: &'input str,
    (_, __0, _): (usize, Box<Term>, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    vec![__0]
}

#[allow(unused_variables)]
pub fn __action13<
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
pub fn __action14<
    'input,
>(
    input: &'input str,
    __0: (usize, Box<Term>, usize),
    __1: (usize, &'input str, usize),
) -> ::std::vec::Vec<Box<Term>>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action11(
        input,
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action12(
        input,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action15<
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
    let __temp0 = __action11(
        input,
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action13(
        input,
        __0,
        __temp0,
    )
}

#[allow(unused_variables)]
pub fn __action16<
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
    let __temp0 = __action9(
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
pub fn __action17<
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
    let __temp0 = __action10(
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
