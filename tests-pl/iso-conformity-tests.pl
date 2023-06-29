:- module(iso_conformity_tests, []).

:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(files)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(lists), [append/3]).

writeq_term_to_chars(Term, Chars) :-
    Options = [ignore_ops(false), numbervars(true), quoted(true), variable_names([])],
    write_term_to_chars(Term, Options, Chars).

write_term_to_chars(Term, Chars) :-
    Options = [ignore_ops(false), numbervars(false), quoted(false), variable_names([])],
    write_term_to_chars(Term, Options, Chars).

write_canonical_term_to_chars(Term, Chars) :-
    Options = [ignore_ops(true), numbervars(false), quoted(true), variable_names([])],
    write_term_to_chars(Term, Options, Chars).

test_syntax_error(ReadString, Error) :-
    catch((once(read_from_chars(ReadString, _)),
           false),
          error(Error, _),
          true).

test_1 :- write_term_to_chars('\n', Chars),
          Chars = "\n".

test_2 :- test_syntax_error("'\n", syntax_error(_)).

test_3 :- test_syntax_error(")\n", syntax_error(incomplete_reduction)).

test_261 :- test_syntax_error(")\n'\n", syntax_error(invalid_single_quoted_character)).

test_4 :- test_syntax_error(".\n", syntax_error(incomplete_reduction)).

test_177 :- test_syntax_error("0'\t=0' .", syntax_error(unexpected_char)).

test_6 :- test_syntax_error("writeq('\n').", syntax_error(invalid_single_quoted_character)).

test_7 :- read_from_chars("writeq('\\\n').", T),
          T == writeq('').

test_8 :- read_from_chars("writeq('\\\na').", T),
          T == writeq(a).

test_9 :- read_from_chars("writeq('a\\\nb').", T),
          T == writeq(ab).

test_10 :- read_from_chars("writeq('a\\\n b').", T),
           T == writeq('a b').

test_11 :- test_syntax_error("writeq('\\ ').", syntax_error(invalid_single_quoted_character)).

test_193 :- test_syntax_error("writeq('\\ \n').", syntax_error(invalid_single_quoted_character)).

test_12 :- test_syntax_error("writeq('\\\t').", syntax_error(invalid_single_quoted_character)).

test_13 :- read_from_chars("writeq('\\t').", T),
           T == writeq('\t').

test_14 :- read_from_chars("writeq('\\a').", T),
           T == writeq('\a').

test_15 :- read_from_chars("writeq('\\7\\').", T),
           T == writeq('\a').

test_16 :- test_syntax_error("writeq('\\ca').", syntax_error(invalid_single_quoted_character)).

test_241 :- test_syntax_error("writeq('\\d').", syntax_error(invalid_single_quoted_character)).

test_17 :- test_syntax_error("writeq('\\e').", syntax_error(invalid_single_quoted_character)).

test_18 :- read_from_chars("writeq('\\033\\').", T),
           T = writeq('\x1b\').

test_301 :- read_from_chars("writeq('\\0\\').", T),
            T = writeq('\x0\').

test_19 :- test_syntax_error("char_code('\\e', C).", syntax_error(invalid_single_quoted_character)).

test_21 :- test_syntax_error("char_code('\\d', C).", syntax_error(invalid_single_quoted_character)).

test_22 :- test_syntax_error("writeq('\\u1').", syntax_error(invalid_single_quoted_character)).

test_23 :- test_syntax_error("X = 0'\\u1.", syntax_error(unexpected_char)).

test_24 :- test_syntax_error("writeq('\n", syntax_error(invalid_single_quoted_character)).

test_25 :- test_syntax_error("writeq(.", syntax_error(incomplete_reduction)).

test_26 :- test_syntax_error("'\\\n''.\n", syntax_error(invalid_single_quoted_character)).

test_210 :- test_syntax_error("X = 0'\\.", syntax_error(unexpected_char)).

test_211 :- test_syntax_error("X = 0'\\. .", syntax_error(unexpected_char)).

test_222 :- writeq_term_to_chars((-)-(-), T),
            T == "(-)-(-)".

test_223 :- writeq_term_to_chars(((:-):-(:-)), T),
            T == "(:-):-(:-)".

test_27 :- writeq_term_to_chars((*)=(*), T),
           T == "(*)=(*)".

test_28 :- writeq_term_to_chars([:-,-], T),
           T == "[:-,-]".

test_29 :- writeq_term_to_chars(f(*), T),
           T == "f(*)".

test_30 :- writeq_term_to_chars(a*(b+c), T),
           T == "a*(b+c)".

test_31 :- writeq_term_to_chars(f(;,'|',';;'), T),
           T == "f(;,'|',';;')".

test_32 :- read_from_chars("[.,.(.,.,.)].", T),
           writeq_term_to_chars(T, Chars),
           Chars == "['.','.'('.','.','.')]".

test_33 :- writeq_term_to_chars((a :- b,c), Chars),
           Chars == "a:-b,c".

test_34 :- write_canonical_term_to_chars([a], T),
           T == "'.'(a,[])".

test_35 :- writeq_term_to_chars('/*', Chars),
           Chars == "'/*'".

test_203 :- writeq_term_to_chars(//*, Chars),
            Chars == "//*".

test_282 :- writeq_term_to_chars(//*.*/, Chars),
            Chars == "//*.*/".

test_36 :- writeq_term_to_chars('/**', Chars),
           Chars == "'/**'".

test_37 :- writeq_term_to_chars('*/', Chars),
           Chars == "*/".

test_38 :- "\'\`\"" = "'`""".

test_179 :- "\'\"" = "'""".

test_178 :- "\`" = "`".

test_39 :- '\'\`\"' = '''`"'.

test_40 :- writeq_term_to_chars('\'\`\"\"', T),
           T == "'\\'`\"\"'".

test_41 :- ('\\') = (\).

test_42 :- setup_call_cleanup(op(1,xf,xf1),
                              (  read_from_chars("1xf1 = xf1(1).", T),
                                 call(T)
                              ),
                              op(0,xf,xf1)).

test_43 :- test_syntax_error("X = 0X1.", syntax_error(incomplete_reduction)).

test_44 :- test_syntax_error("float(.0).", syntax_error(incomplete_reduction)).

test_45 :- setup_call_cleanup(op(100,xfx,.),
                              (  read_from_chars("functor(3 .2,F,A).", T),
                                 call(T),
                                 T == functor('.'(3,2),'.',2)
                              ),
                              op(0,xfx,.)).

test_46 :- test_syntax_error("float(- .0).", syntax_error(incomplete_reduction)).

test_47 :- test_syntax_error("float(1E9).", syntax_error(incomplete_reduction)).

test_48 :- test_syntax_error("integer(1e).", syntax_error(incomplete_reduction)).

test_49 :- setup_call_cleanup(op(9,xf,e9),
                              (  read_from_chars("1e9 = e9(1).", T),
                                 call(T)
                              ),
                              op(0,xf,e9)).

test_50_51_204_220 :-
    setup_call_cleanup(op(9,xf,e),
                       (  read_from_chars("1e-9 = -(e(1),9).", T0),
                          call(T0),
                          read_from_chars("1.0e- 9 = -(e(1.0),9).", T1),
                          call(T1),
                          read_from_chars("1e.", T2),
                          writeq_term_to_chars(T2, T3),
                          T3 == "1 e",
                          read_from_chars("1.0e.", T4),
                          writeq_term_to_chars(T4, T5),
                          T5 == "1.0 e"
                       ),
                       op(0,xf,e)).

test_52 :- setup_call_cleanup(op(9,xfy,e),
                              (  read_from_chars("1.2e 3 = e(X,Y).", T0),
                                 call(T0)
                              ),
                              op(0,xfy,e)).

test_53 :- writeq_term_to_chars(1.0e100, Chars),
           Chars == "1.0e100".

test_54 :- test_syntax_error("float(1.0ee9).", syntax_error(incomplete_reduction)).

test_286 :- (- (1)) = -(1).

test_287 :- (- -1) = -(-1).

test_288 :- (- 1^2) = ^(-1,2).

test_56 :- integer(- 1).

test_57 :- integer('-'1).

test_58 :- integer('-' 1).

test_59 :- integer(- /*.*/1).

test_60 :- test_syntax_error("integer(-/*.*/1).", syntax_error(incomplete_reduction)).

test_61 :- integer('-'/*.*/1).

test_62 :- atom(-/*.*/-).

test_63_180_64 :- setup_call_cleanup((  current_op(P,fy,-),
                                        op(0,fy,-)
                                     ),
                                     (  integer(-1),
                                        integer(- 1)
                                     ),
                                     op(P,fy,-)).

test_135 :- writeq_term_to_chars(-(1), Chars),
            Chars == "- (1)".

test_136 :- setup_call_cleanup((  current_op(P,fy,-),
                                  op(0,fy,-)
                               ),
                               (  writeq_term_to_chars(-(1), Chars),
                                  Chars == "-(1)"
                               ),
                               op(P,fy,-)).

test_182 :- writeq_term_to_chars(-(-1), Chars),
            Chars == "- -1".

test_183 :- writeq_term_to_chars(-(1^2), Chars),
            Chars == "- (1^2)".

test_260 :- writeq_term_to_chars(-(a^2), Chars),
            Chars == "- (a^2)".

test_139 :- writeq_term_to_chars(-((a,b)), Chars),
            Chars == "- (a,b)".

test_218 :- writeq_term_to_chars(-(1*2), Chars),
            Chars == "- (1*2)".

test_140 :- writeq_term_to_chars(-a, Chars),
            Chars == "- a".

test_184 :- writeq_term_to_chars(-(-), Chars),
            Chars == "- (-)".

test_185 :- writeq_term_to_chars(-[-], Chars),
            Chars == "- \"-\"".

test_188 :- writeq_term_to_chars(-p(c), Chars),
            Chars == "- p(c)".

test_189 :- writeq_term_to_chars(-{}, Chars),
            Chars == "- {}".

test_190 :- writeq_term_to_chars(-{a}, Chars),
            Chars == "- {a}".

test_191 :- writeq_term_to_chars(-(-a), Chars),
            Chars == "- - a".

test_192 :- writeq_term_to_chars(-(-(-a)), Chars),
            Chars == "- - - a".

test_216 :- writeq_term_to_chars(-(-1), Chars),
            Chars == "- -1".

test_215_248_249 :-
    setup_call_cleanup(op(100,yfx,~),
                       (  read_from_chars("-(1~2~3).", T0),
                          writeq_term_to_chars(T0, Chars0),
                          Chars0 == "- (1~2~3)",
                          read_from_chars("- (1~2).", T1),
                          writeq_term_to_chars(T1, Chars1),
                          Chars1 == "- (1~2)",
                          read_from_chars("1~2.", T2),
                          writeq_term_to_chars(T2, Chars2),
                          Chars2 == "1~2"
                       ),
                       op(0,yfx,~)).

test_278 :- setup_call_cleanup(op(9,xfy,.),
                               (  writeq_term_to_chars(-[1], Chars),
                                  Chars == "- [1]"
                               ),
                               op(0,xfy,.)).

test_279_296 :-
    setup_call_cleanup(op(9,xf,'$VAR'),
                       (  writeq_term_to_chars(-'$VAR'(0), Chars0),
                          Chars0 == "- A",
                          writeq_term_to_chars('$VAR'(0), Chars1),
                          Chars1 == "A"
                       ),
                       op(0,xf,'$VAR')).

test_55 :- setup_call_cleanup(op(1,yf,yf1),
                              (  read_from_chars("{-1 yf1}={yf1(X)}.", T),
                                 call(T),
                                 T = (_ = { yf1(-1) })
                              ),
                              op(0,yf,yf1)).

test_65 :- compound(+1).

test_66 :- compound(+ 1).

test_277 :- writeq_term_to_chars(+ 1^2, _).

test_67 :- setup_call_cleanup((  current_op(P,fy,+),
                                 op(0,fy,+)
                              ),
                              compound(+1),
                              op(P,fy,+)).

test_257 :- writeq_term_to_chars([+{a},+[]], Chars),
            Chars == "[+ {a},+ []]".

test_68 :- [(:-)|(:-)]=[:-|:-].

test_69 :- test_syntax_error("X=[a|b,c].", syntax_error(incomplete_reduction)).

test_70 :- catch((op(1000,xfy,','),
                  false),
                 error(permission_error(modify, operator, ','), op/3),
                 true).

test_71 :- catch((op(1001,xfy,','),
                  false),
                 error(permission_error(modify, operator, ','), op/3),
                 true).

test_72 :- catch((op(999,xfy,'|'),
                  false),
                 error(permission_error(create, operator, '|'), op/3),
                 true).

test_73 :- _ = [a|b].

test_285 :- test_syntax_error("X = [(a|b)].", syntax_error(_)).

test_219 :- [a|[]] = [a].

test_74 :- test_syntax_error("X = [a|b|c].", syntax_error(incomplete_reduction)).

test_75 :- test_syntax_error("var(a:-b).", syntax_error(incomplete_reduction)).

test_76 :- test_syntax_error(":- = :- .", syntax_error(incomplete_reduction)).

test_77 :- test_syntax_error("- = - .", syntax_error(incomplete_reduction)).

test_78 :- test_syntax_error("* = * .", syntax_error(incomplete_reduction)).

test_79 :- current_op(200,fy,-), !.

test_80 :- current_op(200,fy,+), !.

test_81 :- {- - c}={-(-(c))}.

test_82 :- test_syntax_error("(- -) = -(-). ", syntax_error(incomplete_reduction)).

test_83 :- test_syntax_error("(- - -) = -(-(-)). ", syntax_error(incomplete_reduction)).

test_84 :- test_syntax_error("(- - - -) = -(-(-(-))). ", syntax_error(incomplete_reduction)).

test_85 :- test_syntax_error("{:- :- c} = {:-(:-,c)}.", syntax_error(incomplete_reduction)).

test_86 :- test_syntax_error("{- = - 1}={(-(=)) - 1}. ", syntax_error(incomplete_reduction)).

test_87 :- test_syntax_error("write_canonical((- = - 1)). ", syntax_error(incomplete_reduction)).

test_88 :- test_syntax_error("write_canonical((- = -1)). ", syntax_error(incomplete_reduction)).

test_89 :- test_syntax_error("write_canonical((-;)). ", syntax_error(incomplete_reduction)).

test_90 :- test_syntax_error("write_canonical((-;-)). ", syntax_error(incomplete_reduction)).

test_91 :- test_syntax_error("write_canonical((;-;-)). ", syntax_error(incomplete_reduction)).

test_92 :- test_syntax_error("[:- -c] = [(:- -c)].", syntax_error(incomplete_reduction)).

test_93 :- test_syntax_error("writeq([a,b|,]).", syntax_error(incomplete_reduction)).

test_94 :- test_syntax_error("X = {,}.", syntax_error(incomplete_reduction)).

test_95 :- {1} = {}(1).

test_96 :- write_canonical_term_to_chars({1}, Chars),
           Chars == "{}(1)".

test_97 :- '[]'(1) = [ ](X),
           X == 1.

test_98 :- test_syntax_error("X = [] (1).", syntax_error(incomplete_reduction)).

test_99 :- catch((op(100,yfy,op),
                  false),
                 error(domain_error(operator_specifier, yfy), op/3),
                 true).

test_100 :- '''' = '\''.

test_101 :- a = '\141\'.

test_102 :- test_syntax_error("a = '\\141'.", syntax_error(incomplete_reduction)).

test_103 :- X = '\141\141',
            X == a141.

test_104 :- test_syntax_error("X = '\\9'.", syntax_error(invalid_single_quoted_character)).

test_105 :- test_syntax_error("X = '\\N'.", syntax_error(invalid_single_quoted_character)).

test_106 :- test_syntax_error("X = '\\\\'.", syntax_error(incomplete_reduction)).

test_107 :- test_syntax_error("X = '\\77777777777\\'.", syntax_error(cannot_parse_big_int)).

test_108 :- a = '\x61\'.

test_109 :- test_syntax_error("atom_codes('\\xG\\',Cs).", syntax_error(incomplete_reduction)).

test_110 :- test_syntax_error("atom_codes('\\xG1\\',Cs).", syntax_error(incomplete_reduction)).

test_111 :- test_syntax_error("atom(`).", syntax_error(incomplete_reduction)).

test_112 :- test_syntax_error("atom(`+).", syntax_error(incomplete_reduction)).

test_297 :- test_syntax_error("atom(`\n`).", syntax_error(missing_quote)).

test_113 :- test_syntax_error("X =`a`.", syntax_error(back_quoted_string)).

test_114 :- integer(0'\').

test_115 :- integer(0''').

test_116 :- 0''' = 0'\'.

test_117 :- test_syntax_error("integer(0'').", syntax_error(incomplete_reduction)).

test_195_205_196_197 :-
    setup_call_cleanup(op(100,xf,''),
                       (  read_from_chars("(0 '') = ''(X).", T0),
                          call(T0),
                          T0 = (_ = ('')(0)),
                          read_from_chars("0 ''.", T1),
                          writeq_term_to_chars(T1, C0),
                          C0 == "0 ''",
                          read_from_chars("0''.", T2),
                          writeq_term_to_chars(T2, C1),
                          C1 == "0 ''" ),
                       op(0,xf,'')).

test_118_119_120 :-
    setup_call_cleanup(op(100,xfx,''),
                       (  read_from_chars("functor(0 ''1, F, A).", T0),
                          call(T0),
                          T0 = functor(_, (''), 2),
                          read_from_chars("functor(0''1, F, A).", T1),
                          call(T1),
                          T1 = functor(_, (''), 2)
                       ),
                       op(0,xfx,'')).

test_206_207_209_256 :-
    setup_call_cleanup(op(100,xf,f),
                       (  test_syntax_error("0'f'.", syntax_error(incomplete_reduction)),
                          read_from_chars("0'f'f'.", T0),
                          writeq_term_to_chars(T0, C0),
                          C0 == "102 f",
                          read_from_chars("0'ff.", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "102 f",
                          read_from_chars("0f.", T2),
                          writeq_term_to_chars(T2, C2),
                          C2 == "0 f"
                       ),
                       op(0,xf,f)).

test_208 :- setup_call_cleanup(op(100,xf,'f '),
                               (  read_from_chars("0 'f '.", T0),
                                  writeq_term_to_chars(T0, C0),
                                  C0 == "0 'f '"),
                               op(0,xf,'f ')).

test_121 :- test_syntax_error("X = 2'1.", syntax_error(incomplete_reduction)).

test_122_262 :-
    setup_call_cleanup(op(100,xfx,'1 '),
                       (  read_from_chars("functor(2'1 'y, F, A).", T0),
                          call(T0),
                          T0 = functor(_, ('1 '), 2),
                          read_from_chars("functor(2 '1 'y, F, A).", T1),
                          call(T1),
                          T1 = functor(_, ('1 '), 2)
                       ),
                       op(0,xfx,'1 ')).

test_123 :- read_from_chars("X = 0'\\x41\\ .", T),
            T = (_ = A),
            A == 65.

test_124 :- X =0'\x41\,
            X == 65.

test_125 :- X =0'\x1\,
            X == 1.

test_127 :- X is 16'mod'2,
            X == 0.

test_128 :- X is 37'mod'2,
            X == 1.

test_129 :- test_syntax_error("X is 0'mod'1.", syntax_error(incomplete_reduction)).

test_130 :- X is 1'+'1,
            X == 2.

test_212 :- read_from_chars("X is 1'\\\n+'1.", T),
            T = (_ is 1+1),
            call(T).

test_213 :- read_from_chars("X is 0'\\\n+'1.", T),
            T = (_ is 0+1),
            call(T).

test_259 :- read_from_chars("X = 0'\\\n+'/*'. %*/1.", T),
            T = (_ = 0+1),
            call(T).

test_303 :- test_syntax_error("X = 0'\\\na.", syntax_error(incomplete_reduction)).

test_214 :- test_syntax_error("X is 0'\\", syntax_error(incomplete_reduction)).

test_126 :- test_syntax_error("X = 0'\\\n.\\", syntax_error(incomplete_reduction)).

test_131_132_133 :-
    setup_call_cleanup(op(100,fx,' op'),
                       (  read_from_chars("' op' '1 '.", T0),
                          writeq_term_to_chars(T0, C0),
                          C0 == "' op' '1 '",
                          read_from_chars("' op'[].", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "' op' []"
                       ),
                       op(0, fx, ' op')
                      ).

test_134 :-
    setup_call_cleanup(op(1,xf,xf1),
                       test_syntax_error("{- =xf1}.", syntax_error(incomplete_reduction)),
                       op(0,xf,xf1)).

test_137 :- writeq_term_to_chars(- (a*b), Chars),
            Chars == "- (a*b)".

test_138 :- writeq_term_to_chars(\ (a*b), Chars),
            Chars == "\\ (a*b)".

test_141 :- \+ current_op(_,xfy,.).

test_142_143_144_221_258 :-
    setup_call_cleanup(op(100,xfy,.),
                       (  read_from_chars("1 .2.", T0),
                          writeq_term_to_chars(T0, C0),
                          C0 == "[1|2]",
                          read_from_chars("[1].", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "[1]",
                          read_from_chars("-[1].", T2),
                          writeq_term_to_chars(T2, C2),
                          C2 == "- [1]",
                          read_from_chars("X = 1.e.", T3),
                          writeq_term_to_chars(T3, C3),
                          C3 == "A=[1|e]",
                          read_from_chars("writeq(ok).%\n1=X.", T4),
                          T4 = writeq(ok)
                       ),
                       op(0,xfy,.)).

test_145 :- write_canonical_term_to_chars('$VAR'(0), Cs),
            Cs == "'$VAR'(0)".

test_146 :- write_term_to_chars('$VAR'(0), [], Cs),
            Cs == "$VAR(0)".

test_244 :- writeq_term_to_chars('$VAR'(0), Cs),
            Cs == "A".

test_245 :- writeq_term_to_chars('$VAR'(-1), Cs),
            Cs == "'$VAR'(-1)".

test_246 :- writeq_term_to_chars('$VAR'(-2), Cs),
            Cs == "'$VAR'(-2)".

test_247 :- writeq_term_to_chars('$VAR'(x), Cs),
            Cs == "'$VAR'(x)".

test_289 :- writeq_term_to_chars('$VAR'('A'), Cs),
            Cs == "'$VAR'('A')".

test_147_148_149_150 :-
    setup_call_cleanup((  op(9,fy,fy),
                          op(9,yf,yf)),
                       (  read_from_chars("fy 1 yf.", T0),
                          write_canonical_term_to_chars(T0, C0),
                          C0 == "fy(yf(1))",
                          test_syntax_error("fy yf.", syntax_error(incomplete_reduction)),
                          read_from_chars("fy(yf(1)).", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "fy 1 yf",
                          read_from_chars("yf(fy(1)).", T2),
                          writeq_term_to_chars(T2, C2),
                          C2 == "(fy 1)yf"
                       ),
                       (  op(0,fy,fy),
                          op(0,yf,yf))).

test_151_152_153 :-
    setup_call_cleanup((  op(9,fy,fy),
                          op(9,yfx,yfx)),
                       (  read_from_chars("fy 1 yfx 2.", T0),
                          write_canonical_term_to_chars(T0, C0),
                          C0 == "fy(yfx(1,2))",
                          read_from_chars("fy(yfx(1,2)).", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "fy 1 yfx 2",
                          read_from_chars("yfx(fy(1),2).", T2),
                          writeq_term_to_chars(T2, C2),
                          C2 == "(fy 1)yfx 2"
                       ),
                       (  op(0,fy,fy),
                          op(0,yfx,yfx))).

test_154_155_156 :-
    setup_call_cleanup((  op(9,yf,yf),
                          op(9,xfy,xfy)),
                       (  read_from_chars("1 xfy 2 yf.", T0),
                          write_canonical_term_to_chars(T0, C0),
                          C0 == "xfy(1,yf(2))",
                          read_from_chars("xfy(1,yf(2)).", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "1 xfy 2 yf",
                          read_from_chars("yf(xfy(1,2)).", T2),
                          writeq_term_to_chars(T2, C2),
                          C2 == "(1 xfy 2)yf"
                       ),
                       (  op(0,yf,yf),
                          op(0,xfy,xfy))
                      ).

test_157 :- setup_call_cleanup((( current_op(P,xfy,:-) ->
                                  true
                                ; P = 0
                                ),
                                op(0,xfy,:-)
                               ),
                               \+ current_op(_,xfx,:-),
                               ( op(P,xfy,:-),
                                 op(1200,xfx,:-) )
                              ).

test_158 :- catch((op(0,xfy,','),
                   false),
                  error(permission_error(modify, operator, (',')), op/3),
                  true).

test_159_201_202_160_161 :-
    setup_call_cleanup((  op(9,fy,f),
                          op(9,yf,f)),
                       (  read_from_chars("f f 0.", T0),
                          write_canonical_term_to_chars(T0, C0),
                          C0 == "f(f(0))",
                          read_from_chars("f(f(0)).", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "f f 0",
                          read_from_chars("f 0 f.", T2),
                          write_canonical_term_to_chars(T2, C2),
                          C2 == "f(f(0))",
                          read_from_chars("0 f f.", T3),
                          write_canonical_term_to_chars(T3, C3),
                          C3 == "f(f(0))",
                          test_syntax_error("f f.", syntax_error(incomplete_reduction))
                       ),
                       (  op(0,fy,f),
                          op(0,yf,f))).

test_162 :- setup_call_cleanup((op(9,fy,p),op(9,yfx,p)),
                               test_syntax_error("1 p p p 2.", syntax_error(incomplete_reduction)),
                               (op(0,fy,p),op(0,yfx,p))).

test_163 :- setup_call_cleanup((op(9,fy,p),op(9,xfy,p)),
                               ( read_from_chars("1 p p p 2.", T),
                                 write_canonical_term_to_chars(T, C),
                                 C == "p(1,p(p(2)))"
                               ),
                               (op(0,fy,p),op(0,xfy,p))).

test_164 :- setup_call_cleanup((op(7,fy,p),op(9,yfx,p)),
                               ( read_from_chars("1 p p p 2.", T),
                                 write_canonical_term_to_chars(T, C),
                                 C == "p(1,p(p(2)))"
                               ),
                               (op(0,fy,p),op(0,yfx,p))).

test_165 :- atom('.''-''.').

test_166_167 :- setup_call_cleanup(current_op(P,xfy,'|'),
                                   (  op(0,xfy,'|'),
                                      test_syntax_error("(a|b).", syntax_error(incomplete_reduction))),
                                   op(P,xfy,'|')).

test_168_169 :- call_cleanup((  op(0,xfy,.),
                                op(9,yf,.),
                                read_from_chars(".(.).", T),
                                writeq_term_to_chars(T, C),
                                C == "('.')'.'" ),
                             op(0,yf,.)).

test_194 :- op(0,xfy,.),
            writeq_term_to_chars((.)+(.), C),
            C == "'.'+'.'".

test_170 :- set_prolog_flag(double_quotes,chars).

test_171 :- writeq_term_to_chars("a", C),
            C == "\"a\"".

test_229 :- test_syntax_error("\"\\z.\"", syntax_error(missing_quote)).

test_300 :- writeq_term_to_chars("\0\", C),
            C == "\"\\x0\\\"".

test_172 :- X is 10.0** -323,
            writeq_term_to_chars(X, C),
            C == "1.0e-323".

test_173 :- 1.0e-323=:=10.0** -323.

test_174 :- -1 = -0x1.

test_175 :- T = t(0b1,0o1,0x1),
            T = t(1,1,1).

test_176 :- X is 0b1mod 2,
            X == 1.

test_217_181_290 :-
     setup_call_cleanup((  current_op(P, xfy, '|') ->
                           true
                        ;  P = 0
                        ),
                        (  op(1105,xfy,'|'),
                           read_from_chars("(a-->b,c|d).", T0),
                           writeq_term_to_chars(T0, C0),
                           C0 == "a-->b,c | d",
                           read_from_chars("[(a|b)].", T1),
                           writeq_term_to_chars(T1, C1),
                           C1 == "[(a | b)]"
                        ),
                        op(P, xfy, '|')).

test_186 :- X/* /*/=7,
            X == 7.

test_187 :- X/*/*/=7,
            X == 7.

test_198 :- atom($-).

test_199 :- atom(-$).

test_200 :- setup_call_cleanup(op(900, fy, [$]),
                               (  read_from_chars("$a+b.", T),
                                  write_canonical_term_to_chars(T, C),
                                  C == "$(+(a,b))"
                               ),
                               op(0,fy,[$])).

test_224 :- catch((read_from_chars("\\ .", T),
                   call(T),
                   false),
                  error(existence_error(procedure,(\)/0), _),
                  true).

test_225 :- char_code(C,0),
            writeq_term_to_chars(C, Cs),
            Cs == "'\\x0\\'".

test_250 :- writeq_term_to_chars('\0\', C),
            C == "'\\x0\\'".

test_226 :- write_canonical_term_to_chars(_+_, Cs),
            Cs == "+(A,B)". % note that no variable names are supplied by write_canonical_term_to_chars/2.

test_227 :- write_canonical_term_to_chars(A+A, Cs),
            Cs == "+(A,A)".

test_228 :- test_syntax_error("writeq(0'\\z).", syntax_error(unexpected_char)).

test_230 :- test_syntax_error("char_code('\\^',X).", syntax_error(invalid_single_quoted_character)).

test_231 :- test_syntax_error("writeq(0'\\c).", syntax_error(unexpected_char)).

test_232 :- test_syntax_error("writeq(0'\\ ).", syntax_error(unexpected_char)).

test_233 :- test_syntax_error("writeq(nop (1)).", syntax_error(incomplete_reduction)).

test_234_235 :- setup_call_cleanup(op(400,fx,f),
                                   (  read_from_chars("f/*.*/(1,2).", T),
                                      writeq_term_to_chars(T, C),
                                      C == "f (1,2)",
                                      test_syntax_error("1 = f.", syntax_error(incomplete_reduction))
                                   ),
                                   op(0,fx,f)).

test_236 :- write_canonical_term_to_chars(a- - -b, Cs),
            Cs == "-(a,-(-(b)))".

test_237 :- catch((op(699,xf,>),
                   false),
                  error(permission_error(create,operator,>),op/3),
                  true).

test_238 :- writeq_term_to_chars(>(>(a),b), Cs),
            Cs == ">(a)>b".

test_239 :- test_syntax_error("a> >b.", syntax_error(incomplete_reduction)).

test_242 :- test_syntax_error("a> =b.", syntax_error(incomplete_reduction)).

test_243 :- test_syntax_error("a>,b.", syntax_error(incomplete_reduction)).

test_240 :- test_syntax_error("a>.", syntax_error(incomplete_reduction)).

test_251_263_252_253_254_255 :-
    setup_call_cleanup(op(9,yfx,[bop,bo,b,op,xor]),
                       (  read_from_chars("0 bop 2.", T0),
                          writeq_term_to_chars(T0, C0),
                          C0 == "0 bop 2",
                          read_from_chars("0bo 2.", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "0 bo 2",
                          read_from_chars("0b 2.", T2),
                          writeq_term_to_chars(T2, C2),
                          C2 == "0 b 2",
                          read_from_chars("0op 2.", T3),
                          writeq_term_to_chars(T3, C3),
                          C3 == "0 op 2",
                          read_from_chars("0xor 2.", T4),
                          writeq_term_to_chars(T4, C4),
                          C4 == "0 xor 2"
                       ),
                       op(0,yfx,[bop,bo,b,op,xor])).

test_264 :- writeq_term_to_chars('^`', C),
            C == "'^`'".

test_265_266_267 :-
    setup_call_cleanup(op(9,yf,[b2,o8]),
                       (  read_from_chars("0b2.", T0),
                          writeq_term_to_chars(T0, C0),
                          C0 == "0 b2",
                          read_from_chars("0o8.", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "0 o8"
                       ),
                       op(0,yf,[b2,o8])).

test_268 :- catch((op(500,xfy,{}),
                   false),
                  error(permission_error(create, operator, {}), op/3),
                  true).

test_269 :- writeq_term_to_chars('\b\r\f\t\n', C),
            C == "'\\b\\r\\f\\t\\n'".

test_270 :-
    setup_call_cleanup((open("test_270.txt", write, WriteFile),
                        format(WriteFile, "get_char(Stream, C). %\n", []),
                        close(WriteFile),
                        open("test_270.txt", read, ReadFile)),
                       (read_term(ReadFile, T, []),
                        T = get_char(ReadFile, C),
                        call(T),
                        C == ' '),
                       (close(ReadFile),
                        delete_file("test_270.txt"))).

test_271 :-
    setup_call_cleanup((open("test_271.txt", write, WriteFile),
                        format(WriteFile, "get_char(Stream, C).%\n", []),
                        close(WriteFile),
                        open("test_271.txt", read, ReadFile)),
                       (read_term(ReadFile, T, []),
                        T = get_char(ReadFile, C),
                        call(T),
                        C == '%'),
                       (close(ReadFile),
                        delete_file("test_271.txt"))).

test_272 :- test_syntax_error("writeq(0B1).", syntax_error(incomplete_reduction)).

test_274_275 :-
    setup_call_cleanup(op(20,fx,--),
                       (  read_from_chars("--(a).", T0),
                          writeq_term_to_chars(T0, C0),
                          C0 == "-- a",
                          op(0,fx,--),
                          read_from_chars("--(a).", T1),
                          writeq_term_to_chars(T1, C1),
                          C1 == "--(a)"
                       ),
                       op(0,fx,--)).

test_276 :- writeq_term_to_chars(0xamod 2, C),
            C == "10 mod 2".

test_280 :- writeq_term_to_chars(00'+'1, C),
            C == "0+1".

test_281 :- test_syntax_error("00'a.", syntax_error(incomplete_reduction)).

test_284 :- test_syntax_error("'\\^J'.", syntax_error(invalid_single_quoted_character)).

test_291 :- writeq_term_to_chars([(a,b)], C),
            C == "[(a,b)]".

test_292 :- writeq_term_to_chars(1 = \\, C),
            C == "1= \\\\".

test_293 :- test_syntax_error("writeq((,)).", syntax_error(incomplete_reduction)).

test_294 :- test_syntax_error("writeq({[}).", syntax_error(incomplete_reduction)).

test_295 :- test_syntax_error("writeq({(}).", syntax_error(incomplete_reduction)).

test_298 :- writeq_term_to_chars([a,b|c], C),
            C == "[a,b|c]".

test_299 :- (\+ (a,b)) = \+(T),
            T == (a,b).

test_302 :- [] = '[]'.

test_304 :- setup_call_cleanup(op(300,fy,~),
                               (  read_from_chars("~ (a = b).", T),
                                  writeq_term_to_chars(T, C),
                                  C == "~ (a=b)"
                               ),
                               op(0,fy,~)).

test_305 :- writeq_term_to_chars(\ (a = b), C),
            C == "\\ (a=b)".

test_306 :- writeq_term_to_chars(+ (a = b), C),
            C == "+ (a=b)".

test_307 :- writeq_term_to_chars([/**/], C),
            C == "[]".

test_308 :- writeq_term_to_chars(.+, C),
            C == ".+".

test_309 :- writeq_term_to_chars({a,b}, C),
            C == "{a,b}".

test_310 :- test_syntax_error("writeq({\\+ (}).", syntax_error(incomplete_reduction)).

test_311 :- test_syntax_error("Finis ().", syntax_error(incomplete_reduction)).

run_tests([Test|Tests]) -->
    (  { call(Test) } ->
       []
    ;  { format("~a failed!~n", [Test]) },
       [Test]
    ),
    run_tests(Tests).
run_tests([]) --> [].

run_tests :-
    findall(Test,
            ( current_predicate(iso_conformity_tests:Test/0),
              once(sub_atom(Test, 0, 5, _, test_))
            ),
            Tests),
    phrase(run_tests(Tests), FailedTests),
    (  FailedTests == [] ->
       write('All tests passed'),
       nl
    ;  format("Failed ISO conformity tests: ~w~n", [FailedTests]),
       false
    ).

% FIXME: enable once all tests pass.
% :- initialization_goals(run_tests).
