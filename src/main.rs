mod l2;

use l2::ast::*;
use l2::codegen::*;
use l2::machine::*;

use std::io::{self, Write};

fn submit(wam: &mut Machine, buffer: String) -> bool {
    let result = l2::l2_parser::parse_TopLevel(&*buffer);

    let mut cg = CodeGenerator::new();

    match &result {
        &Ok(TopLevel::Fact(ref fact)) => {
            let compiled_fact = cg.compile_fact(&fact);
            wam.add_fact(fact, compiled_fact);
        },
        &Ok(TopLevel::Rule(ref rule)) => {
            let compiled_rule = cg.compile_rule(&rule);
            wam.add_rule(rule, compiled_rule);
        },
        &Ok(TopLevel::Query(ref query)) => {
            let compiled_query = cg.compile_query(&query);
            let output = wam.run_query(compiled_query, &cg);

            match output {
                Some(result) => {
                    println!("yes");

                    if result != "" {
                        println!("{}", result);
                    }
                },
                None => println!("no")
            }
        },
        &Err(_) => println!("Grammatical error of some kind!"),
    };

    let result = wam.failed();
    wam.reset();
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[inline]
    fn submit_ss(wam: &mut Machine, buffer: &'static str) -> bool {
        submit(wam, String::from(buffer))
    }

    #[test]
    fn test_queries_on_facts() {
        let mut wam = Machine::new();

        submit_ss(&mut wam, "p(Z, Z).");
        submit_ss(&mut wam, "clouds(are, nice).");

        // submit_ss returns true on failure, false on success.
        assert_eq!(submit_ss(&mut wam, "?- p(Z, Z)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(Z, z)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(Z, w)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(z, w)."), true);
        assert_eq!(submit_ss(&mut wam, "?- p(w, w)."), false);
        assert_eq!(submit_ss(&mut wam, "?- clouds(Z, Z)."), true);
        assert_eq!(submit_ss(&mut wam, "?- clouds(are, Z)."), false);
        assert_eq!(submit_ss(&mut wam, "?- clouds(Z, nice)."), false);

        assert_eq!(submit_ss(&mut wam, "?- p(Z, h(Z, W), f(W))."), true);

        submit_ss(&mut wam, "p(Z, h(Z, W), f(W)).");

        assert_eq!(submit_ss(&mut wam, "?- p(z, h(z, z), f(w))."), true);
        assert_eq!(submit_ss(&mut wam, "?- p(z, h(z, w), f(w))."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(z, h(z, W), f(w))."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(Z, h(Z, w), f(Z))."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(z, h(Z, w), f(Z))."), true);

        submit_ss(&mut wam, "p(f(X), h(Y, f(a)), Y).");

        assert_eq!(submit_ss(&mut wam, "?- p(Z, h(Z, W), f(W))."), false);
    }

    #[test]
    fn test_queries_on_rules() {
        let mut wam = Machine::new();

        submit_ss(&mut wam, "p(X, Y) :- q(X, Z), r(Z, Y).");
        submit_ss(&mut wam, "q(q, s).");
        submit_ss(&mut wam, "r(s, t).");

        assert_eq!(submit_ss(&mut wam, "?- p(X, Y)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(q, t)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(t, q)."), true);
        assert_eq!(submit_ss(&mut wam, "?- p(q, T)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(Q, t)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(t, t)."), true);

        submit_ss(&mut wam, "p(X, Y) :- q(f(f(X)), R), r(S, T).");
        submit_ss(&mut wam, "q(f(f(X)), r).");

        assert_eq!(submit_ss(&mut wam, "?- p(X, Y)."), false);

        submit_ss(&mut wam, "q(f(f(x)), r).");

        assert_eq!(submit_ss(&mut wam, "?- p(X, Y)."), false);

        submit_ss(&mut wam, "p(X, Y) :- q(X, Y), r(X, Y).");
        submit_ss(&mut wam, "q(s, t).");
        submit_ss(&mut wam, "r(X, Y) :- r(a).");
        submit_ss(&mut wam, "r(a).");

        assert_eq!(submit_ss(&mut wam, "?- p(X, Y)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(t, S)."), true);
        assert_eq!(submit_ss(&mut wam, "?- p(t, s)."), true);
        assert_eq!(submit_ss(&mut wam, "?- p(s, T)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(S, t)."), false);

        submit_ss(&mut wam, "p(f(f(a), g(b), X), g(b), h) :- q(X, Y).");
        submit_ss(&mut wam, "q(X, Y).");

        assert_eq!(submit_ss(&mut wam, "?- p(f(X, Y, Z), g(b), h)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(f(X, g(Y), Z), g(Z), X)."), true);
        assert_eq!(submit_ss(&mut wam, "?- p(f(X, g(Y), Z), g(Z), h)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(Z, Y, X)."), false);
        assert_eq!(submit_ss(&mut wam, "?- p(f(X, Y, Z), Y, h)."), false);
    }
}

fn l2_repl() {
    let mut wam = Machine::new();

    loop {
        print!("l2> ");

        let _ = io::stdout().flush();
        let mut buffer = String::new();

        io::stdin().read_line(&mut buffer).unwrap();

        if &*buffer == "quit\n" {
            break;
        } else if &*buffer == "clear\n" {
            wam = Machine::new();
            continue;
        }

        submit(&mut wam, buffer);
    }
}

fn main() {
    l2_repl();
}
