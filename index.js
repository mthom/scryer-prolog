import init, { eval_code } from './pkg/scryer_prolog.js';

const run = async () => {
    await init("./pkg/scryer_prolog_bg.wasm");
    let code = `
    :- use_module(library(debug)).
    :- use_module(library(format)).
    
    hello_world :- write('Hello World!'), nl.
    
    :- initialization(hello_world).
    `;
    code = `
    :- use_module(library(format)).
    :- use_module(library(clpz)).
    :- use_module(library(lists)).
    
    sudoku(Rows) :-
       length(Rows, 9), maplist(same_length(Rows), Rows),
       append(Rows, Vs), Vs ins 1..9,
       maplist(all_distinct, Rows),
       transpose(Rows, Columns),
       maplist(all_distinct, Columns),
       Rows = [As,Bs,Cs,Ds,Es,Fs,Gs,Hs,Is],
       blocks(As, Bs, Cs),
       blocks(Ds, Es, Fs),
       blocks(Gs, Hs, Is).
    
    blocks([], [], []).
    blocks([N1,N2,N3|Ns1], [N4,N5,N6|Ns2], [N7,N8,N9|Ns3]) :-
       all_distinct([N1,N2,N3,N4,N5,N6,N7,N8,N9]),
       blocks(Ns1, Ns2, Ns3).
    
    problem(1, [[_,_,_,_,_,_,_,_,_],
                [_,_,_,_,_,3,_,8,5],
                [_,_,1,_,2,_,_,_,_],
                [_,_,_,5,_,7,_,_,_],
                [_,_,4,_,_,_,1,_,_],
                [_,9,_,_,_,_,_,_,_],
                [5,_,_,_,_,_,_,7,3],
                [_,_,2,_,1,_,_,_,_],
                [_,_,_,_,4,_,_,_,9]]).
    
    main :-
       problem(1, Rows), sudoku(Rows), maplist(portray_clause, Rows).
    
    :- initialization(main).
    `;
    const result = eval_code(code);
    document.body.textContent = `result: ${result}`;
}
run();
