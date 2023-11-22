/** Predicates for the WebAssembly platform

This module contains predicates that are only available in
the WASM (WebAssembly) version of Scryer Prolog.
*/

:- module(wasm, [js_eval/2]).

:- use_module(library(error)).

%% js_eval(+JsCode, -Result).
%
% Executes a JavaScript snippet `JsCode` using the platform
% `eval` function. `Result` takes the return value of that code.
% Strings, booleans, numbers, null and undefined are directly mapped to Prolog.
% Arrays, objects, bigints, symbols and functions are not mapped.
% Instead, a `js_{type}` atom will be returned.
%
% Example (on a browser):
%
% ```
% ?- js_eval("prompt('What is your name?')", Name).
%    % A prompt is showed, with a textbox.
%    Name = "Whatever was written on the textbox".
% ```
js_eval(JsCode, Result) :-
    must_be(chars, JsCode),
    can_be(chars, Result),
    '$js_eval'(JsCode, Result).
