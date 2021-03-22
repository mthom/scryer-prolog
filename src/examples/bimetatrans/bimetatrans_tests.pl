:- module(bimetatrans_tests, [test_bimetatrans/0]).

:- use_module(bimetatrans).

:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(si)).

/* test(N, Prolog, XML) is expanded to the predicates
 *
 * prolog2ruleml_N :- parse_ruleml(Prolog, XML0), XML0 = XML.
 * ruleml2prolog_N :- parse_ruleml(Prolog0, XML), Prolog0 = Prolog.
 *
 * test_N :- prolog2ruleml_N, ruleml2prolog_N, !.
 * test_N :- throw(error(test_failure, test_N)).
 *
 * which test the invertibility of parse_ruleml/2.
 *
 * The initialization goal is a chain of calls to the test_N in
 * order of ascending N.
 */

until_non_space_or_end([C|Cs], Cs1) :-
    (  C == (' ') ->
       until_non_space_or_end(Cs, Cs1)
    ;  Cs1 = [C|Cs]
    ).
until_non_space_or_end([], []).


strip_indentation(Cs, String) :-
    strip_indentation_(Cs, Cs1),
    partial_string(Cs1, String, []).

strip_indentation_([C|Cs], Cs0) :-
    (  C == ('>') ->
       until_non_space_or_end(Cs, Cs1),
       Cs0 = [C|Cs2],
       strip_indentation_(Cs1, Cs2)
    ;  Cs0 = [C|Cs1],
       strip_indentation_(Cs, Cs1)
    ).
strip_indentation_([], []).


user:term_expansion(Term0, Term) :-
    nonvar(Term0),
    Term0 = test(N, Assert, Query, XML),
    integer(N),
    list_si(Assert),
    list_si(Query),
    partial_string(XML),
    number_chars(N, NChars),
    atom_chars(NAtom, NChars),
    atom_concat(prolog2ruleml_, NAtom, Prolog2RuleML),
    atom_concat(ruleml2prolog_, NAtom, RuleML2Prolog),
    atom_concat(test_, NAtom, TestN),
    strip_indentation(XML, XML1),
    Term = [(Prolog2RuleML :- parse_ruleml(Assert, Query, XML0),
                              XML0 = XML1),
            (RuleML2Prolog :- parse_ruleml(Assert0, Query0, XML),
                              Assert0 = Assert,
                              Query0 = Query),
            (TestN :- write(test(N)), nl, Prolog2RuleML, RuleML2Prolog, !),
            (TestN :- throw(error(test_failure, TestN)))].


test(1,
     [people('Alex',male),people('Alex',female),people('Siri',female)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>people</Rel>\
                <Ind>Alex</Ind>\
                <Data iso:type=\"symbol\">male</Data>\
        </Atom>\
        <Atom>\
                <Rel>people</Rel>\
                <Ind>Alex</Ind>\
                <Data iso:type=\"symbol\">female</Data>\
        </Atom>\
        <Atom>\
                <Rel>people</Rel>\
                <Ind>Siri</Ind>\
                <Data iso:type=\"symbol\">female</Data>\
        </Atom>\
     </Assert>").

test(2,
     [parent('Alex','Mary')],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>parent</Rel>\
                <Ind>Alex</Ind>\
                <Ind>Mary</Ind>\
        </Atom>\
     </Assert>").

test(3,
     [people('Alex',male),people('Alex',female),people('Siri',female),parent('Alex','Mary'),parent('Mary','Tom')],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>people</Rel>\
                <Ind>Alex</Ind>\
                <Data iso:type=\"symbol\">male</Data>\
        </Atom>\
        <Atom>\
                <Rel>people</Rel>\
                <Ind>Alex</Ind>\
                <Data iso:type=\"symbol\">female</Data>\
        </Atom>\
        <Atom>\
                <Rel>people</Rel>\
                <Ind>Siri</Ind>\
                <Data iso:type=\"symbol\">female</Data>\
        </Atom>\
        <Atom>\
                <Rel>parent</Rel>\
                <Ind>Alex</Ind>\
                <Ind>Mary</Ind>\
        </Atom>\
        <Atom>\
                <Rel>parent</Rel>\
                <Ind>Mary</Ind>\
                <Ind>Tom</Ind>\
        </Atom>\
     </Assert>").

test(4,
     [(ancestor(mark, terry) :- true)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>ancestor</Rel>\
                                <Data iso:type=\"symbol\">mark</Data>\
                                <Data iso:type=\"symbol\">terry</Data>\
                        </Atom>\
                </then>\
                <if>\
                        <Atom>\
                                <Rel>true</Rel>\
                        </Atom>\
                </if>\
        </Implies>\
      </Assert>").

test(5,
     [(ancestor(mark, '$V'(y)) :- parent(mark, '$V'(x)), ancestor('$V'(x), '$V'(y)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>ancestor</Rel>\
                                <Data iso:type=\"symbol\">mark</Data>\
                                <Var>y</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>parent</Rel>\
                                        <Data iso:type=\"symbol\">mark</Data>\
                                        <Var>x</Var>\
                                </Atom>\
                                <Atom>\
                                        <Rel>ancestor</Rel>\
                                        <Var>x</Var>\
                                        <Var>y</Var>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(6,
     [(ancestor(mark, terry) :- condition_1, condition_2)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>ancestor</Rel>\
                                <Data iso:type=\"symbol\">mark</Data>\
                                <Data iso:type=\"symbol\">terry</Data>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>condition_1</Rel>\
                                </Atom>\
                                <Atom>\
                                        <Rel>condition_2</Rel>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
      </Assert>").

test(7,
     [(roots(nationality('$V'(x), '$V'(nation)), '$V'(y)) :- parent('$V'(x), '$V'(y)), nationality('$V'(y), '$V'(nation)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>roots</Rel>\
                                <Expr>\
                                        <Fun>nationality</Fun>\
                                        <Var>x</Var>\
                                        <Var>nation</Var>\
                                </Expr>\
                                <Var>y</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>parent</Rel>\
                                        <Var>x</Var>\
                                        <Var>y</Var>\
                                </Atom>\
                                <Atom>\
                                        <Rel>nationality</Rel>\
                                        <Var>y</Var>\
                                        <Var>nation</Var>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(8,
     [a(item), b(item), c(item)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>a</Rel>\
                <Data iso:type=\"symbol\">item</Data>\
        </Atom>\
        <Atom>\
                <Rel>b</Rel>\
                <Data iso:type=\"symbol\">item</Data>\
        </Atom>\
        <Atom>\
                <Rel>c</Rel>\
                <Data iso:type=\"symbol\">item</Data>\
        </Atom>\
      </Assert>").

test(9,
     [number(1)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>number</Rel>\
                <Data iso:type=\"number\">1</Data>\
        </Atom>\
     </Assert>").

test(10,
     [number(1.2)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>number</Rel>\
                <Data iso:type=\"number\">1.2</Data>\
        </Atom>\
      </Assert>").

test(11,
     [number(-1.2)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>number</Rel>\
                <Data iso:type=\"number\">-1.2</Data>\
        </Atom>\
      </Assert>").

test(12,
     [h(f(1,2,g(b)), '$V'(stuff))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>h</Rel>\
                <Expr>\
                        <Fun>f</Fun>\
                        <Data iso:type=\"number\">1</Data>\
                        <Data iso:type=\"number\">2</Data>\
                        <Expr>\
                                <Fun>g</Fun>\
                                <Data iso:type=\"symbol\">b</Data>\
                        </Expr>\
                </Expr>\
                <Var>stuff</Var>\
        </Atom>\
      </Assert>").

test(13,
     [buy('$V'(person), '$V'(merchant), book(('$V'(title) | '$V'(info))))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>buy</Rel>\
                <Var>person</Var>\
                <Var>merchant</Var>\
                <Expr>\
                        <Fun>book</Fun>\
                        <Var>title</Var>\
                        <repo>\
                                <Var>info</Var>\
                        </repo>\
                </Expr>\
        </Atom>\
     </Assert>").

test(14,
     [(own('$V'(person),book(('$V'(title) | '$V'(info)))):-buy('$V'(person),'$V'(merchant),book(('$V'(title) | '$V'(info)))),\+relinquish('$V'(person),book(('$V'(title) | '$V'(info))))),buy('Mary','John',book('XML Bible','Elliotte Rusty Harold',2001))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>own</Rel>\
                                <Var>person</Var>\
                                <Expr>\
                                        <Fun>book</Fun>\
                                        <Var>title</Var>\
                                        <repo>\
                                                <Var>info</Var>\
                                        </repo>\
                                </Expr>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>buy</Rel>\
                                        <Var>person</Var>\
                                        <Var>merchant</Var>\
                                        <Expr>\
                                                <Fun>book</Fun>\
                                                <Var>title</Var>\
                                                <repo>\
                                                        <Var>info</Var>\
                                                </repo>\
                                        </Expr>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>relinquish</Rel>\
                                                <Var>person</Var>\
                                                <Expr>\
                                                        <Fun>book</Fun>\
                                                        <Var>title</Var>\
                                                        <repo>\
                                                                <Var>info</Var>\
                                                        </repo>\
                                                </Expr>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
        <Atom>\
                <Rel>buy</Rel>\
                <Ind>Mary</Ind>\
                <Ind>John</Ind>\
                <Expr>\
                        <Fun>book</Fun>\
                        <Ind>XML Bible</Ind>\
                        <Ind>Elliotte Rusty Harold</Ind>\
                        <Data iso:type=\"number\">2001</Data>\
                </Expr>\
        </Atom>\
      </Assert>").


test(15,
     [(fact :- \+ blue_eyed(mark))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>fact</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <Naf>\
                                <Atom>\
                                        <Rel>blue_eyed</Rel>\
                                        <Data iso:type=\"symbol\">mark</Data>\
                                </Atom>\
                        </Naf>\
                </if>\
        </Implies>\
     </Assert>").

test(16,
     [string_data("string data")],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>string_data</Rel>\
                <Data iso:type=\"string\">\"string data\"</Data>\
        </Atom>\
     </Assert>").

test(17,
     [factorial(0) = 1],
     [],
     "<Assert mapClosure=\"universal\">\
        <Equal>\
                <Expr>\
                        <Fun>factorial</Fun>\
                        <Data iso:type=\"number\">0</Data>\
                </Expr>\
                <Data iso:type=\"number\">1</Data>\
        </Equal>\
      </Assert>").

test(18,
     [factorial(n) = mul(n, factorial(sub(n,1)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Equal>\
                <Expr>\
                        <Fun>factorial</Fun>\
                        <Data iso:type=\"symbol\">n</Data>\
                </Expr>\
                <Expr>\
                        <Fun>mul</Fun>\
                        <Data iso:type=\"symbol\">n</Data>\
                        <Expr>\
                                <Fun>factorial</Fun>\
                                <Expr>\
                                        <Fun>sub</Fun>\
                                        <Data iso:type=\"symbol\">n</Data>\
                                        <Data iso:type=\"number\">1</Data>\
                                </Expr>\
                        </Expr>\
                </Expr>\
        </Equal>\
      </Assert>").

test(19,
     [factorial(0) = 1, factorial(n) = mul(n,factorial(sub(n,1)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Equal>\
                <Expr>\
                        <Fun>factorial</Fun>\
                        <Data iso:type=\"number\">0</Data>\
                </Expr>\
                <Data iso:type=\"number\">1</Data>\
        </Equal>\
        <Equal>\
                <Expr>\
                        <Fun>factorial</Fun>\
                        <Data iso:type=\"symbol\">n</Data>\
                </Expr>\
                <Expr>\
                        <Fun>mul</Fun>\
                        <Data iso:type=\"symbol\">n</Data>\
                        <Expr>\
                                <Fun>factorial</Fun>\
                                <Expr>\
                                        <Fun>sub</Fun>\
                                        <Data iso:type=\"symbol\">n</Data>\
                                        <Data iso:type=\"number\">1</Data>\
                                </Expr>\
                        </Expr>\
                </Expr>\
        </Equal>\
      </Assert>").

test(20,
     [(visit('$V'(customer), store(best_buy, manager(karen), location(prospect_st))) :- feels_like_it('$V'(customer)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>visit</Rel>\
                                <Var>customer</Var>\
                                <Expr>\
                                        <Fun>store</Fun>\
                                        <Data iso:type=\"symbol\">best_buy</Data>\
                                        <Expr>\
                                                <Fun>manager</Fun>\
                                                <Data iso:type=\"symbol\">karen</Data>\
                                        </Expr>\
                                        <Expr>\
                                                <Fun>location</Fun>\
                                                <Data iso:type=\"symbol\">prospect_st</Data>\
                                        </Expr>\
                                </Expr>\
                        </Atom>\
                </then>\
                <if>\
                        <Atom>\
                                <Rel>feels_like_it</Rel>\
                                <Var>customer</Var>\
                        </Atom>\
                </if>\
        </Implies>\
      </Assert>").


test(21,
     [(visit('$V'(customer), store(best_buy, manager(karen), location(prospect_st))) :- feels_like_it('$V'(customer)), has_car('$V'(customer)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>visit</Rel>\
                                <Var>customer</Var>\
                                <Expr>\
                                        <Fun>store</Fun>\
                                        <Data iso:type=\"symbol\">best_buy</Data>\
                                        <Expr>\
                                                <Fun>manager</Fun>\
                                                <Data iso:type=\"symbol\">karen</Data>\
                                        </Expr>\
                                        <Expr>\
                                                <Fun>location</Fun>\
                                                <Data iso:type=\"symbol\">prospect_st</Data>\
                                        </Expr>\
                                </Expr>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>feels_like_it</Rel>\
                                        <Var>customer</Var>\
                                </Atom>\
                                <Atom>\
                                        <Rel>has_car</Rel>\
                                        <Var>customer</Var>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
      </Assert>").


test(22,
     [(visit('$V'(customer), store(best_buy, manager((karen | head_office_mgrs)), location(prospect_st))) :- feels_like_it('$V'(customer)), has_car('$V'(customer)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>visit</Rel>\
                                <Var>customer</Var>\
                                <Expr>\
                                        <Fun>store</Fun>\
                                        <Data iso:type=\"symbol\">best_buy</Data>\
                                        <Expr>\
                                                <Fun>manager</Fun>\
                                                <Data iso:type=\"symbol\">karen</Data>\
                                                <repo>\
                                                        <Data iso:type=\"symbol\">head_office_mgrs</Data>\
                                                </repo>\
                                        </Expr>\
                                        <Expr>\
                                                <Fun>location</Fun>\
                                                <Data iso:type=\"symbol\">prospect_st</Data>\
                                        </Expr>\
                                </Expr>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>feels_like_it</Rel>\
                                        <Var>customer</Var>\
                                </Atom>\
                                <Atom>\
                                        <Rel>has_car</Rel>\
                                        <Var>customer</Var>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(23,
     [employee('William'),'Bill'='William'],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>employee</Rel>\
                <Ind>William</Ind>\
        </Atom>\
        <Equal>\
                <Ind>Bill</Ind>\
                <Ind>William</Ind>\
        </Equal>\
      </Assert>").

test(24,
     ['$V'(x)='$V'(x)],
     [],
    "<Assert mapClosure=\"universal\">\
        <Equal>\
                <Var>x</Var>\
                <Var>x</Var>\
        </Equal>\
     </Assert>").

test(25,
     [(s :- p, q, r)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>s</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>p</Rel>\
                                </Atom>\
                                <Atom>\
                                        <Rel>q</Rel>\
                                </Atom>\
                                <Atom>\
                                        <Rel>r</Rel>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(26,
     [(trip(origin(us), destination(tuva)) :- airline_tickets('$V'(airline)), \+ expensive_tickets)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>trip</Rel>\
                                <Expr>\
                                        <Fun>origin</Fun>\
                                        <Data iso:type=\"symbol\">us</Data>\
                                </Expr>\
                                <Expr>\
                                        <Fun>destination</Fun>\
                                        <Data iso:type=\"symbol\">tuva</Data>\
                                </Expr>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>airline_tickets</Rel>\
                                        <Var>airline</Var>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>expensive_tickets</Rel>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(27,
     [(or :- (a ; b))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>or</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <Or>\
                                <Atom>\
                                        <Rel>a</Rel>\
                                </Atom>\
                                <Atom>\
                                        <Rel>b</Rel>\
                                </Atom>\
                        </Or>\
                </if>\
        </Implies>\
     </Assert>").

test(28,
     [(or_and :- (a ; b), c)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>or_and</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <Atom>\
                                                <Rel>a</Rel>\
                                        </Atom>\
                                        <Atom>\
                                                <Rel>b</Rel>\
                                        </Atom>\
                                </Or>\
                                <Atom>\
                                        <Rel>c</Rel>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(29,
     [(or_and_2 :- (a ; b, c), d)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>or_and_2</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <Atom>\
                                                <Rel>a</Rel>\
                                        </Atom>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(30,
     [(or_and_2_equal :- (a ; b, c), d, (factorial(0) = factorial(0)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>or_and_2_equal</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <Atom>\
                                                <Rel>a</Rel>\
                                        </Atom>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Equal>\
                                        <Expr>\
                                                <Fun>factorial</Fun>\
                                                <Data iso:type=\"number\">0</Data>\
                                        </Expr>\
                                        <Expr>\
                                                <Fun>factorial</Fun>\
                                                <Data iso:type=\"number\">0</Data>\
                                        </Expr>\
                                </Equal>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(31,
     [(or_and_3_equal :- (a ; b, c), d, \+ p(a))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>or_and_3_equal</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <Atom>\
                                                <Rel>a</Rel>\
                                        </Atom>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>p</Rel>\
                                                <Data iso:type=\"symbol\">a</Data>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(32,
     [(or_and_4_equal :- (a ; b, c), d, \+ p(a,b,c))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>or_and_4_equal</Rel>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <Atom>\
                                                <Rel>a</Rel>\
                                        </Atom>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>p</Rel>\
                                                <Data iso:type=\"symbol\">a</Data>\
                                                <Data iso:type=\"symbol\">b</Data>\
                                                <Data iso:type=\"symbol\">c</Data>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(33,
     [((term_0 = term_1) :- (a ; b, c), d, \+ p(a,b,c))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Equal>\
                                <Expr>\
                                        <Fun>term_0</Fun>\
                                </Expr>\
                                <Expr>\
                                        <Fun>term_1</Fun>\
                                </Expr>\
                        </Equal>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <Atom>\
                                                <Rel>a</Rel>\
                                        </Atom>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>p</Rel>\
                                                <Data iso:type=\"symbol\">a</Data>\
                                                <Data iso:type=\"symbol\">b</Data>\
                                                <Data iso:type=\"symbol\">c</Data>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(34,
     [((term_0 = term_1) :- (a, f, g ; b, c), d, \+ p(f(a, 1),b,c))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Equal>\
                                <Expr>\
                                        <Fun>term_0</Fun>\
                                </Expr>\
                                <Expr>\
                                        <Fun>term_1</Fun>\
                                </Expr>\
                        </Equal>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>a</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>f</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>g</Rel>\
                                                </Atom>\
                                        </And>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>p</Rel>\
                                                <Expr>\
                                                        <Fun>f</Fun>\
                                                        <Data iso:type=\"symbol\">a</Data>\
                                                        <Data iso:type=\"number\">1</Data>\
                                                </Expr>\
                                                <Data iso:type=\"symbol\">b</Data>\
                                                <Data iso:type=\"symbol\">c</Data>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(35,
     [((term_0(a,1.2,"string") = term_1) :- (a, f, g ; b, c), d, \+ p(f(a, 1),b,c))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Equal>\
                                <Expr>\
                                        <Fun>term_0</Fun>\
                                        <Data iso:type=\"symbol\">a</Data>\
                                        <Data iso:type=\"number\">1.2</Data>\
                                        <Data iso:type=\"string\">\"string\"</Data>\
                                </Expr>\
                                <Expr>\
                                        <Fun>term_1</Fun>\
                                </Expr>\
                        </Equal>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>a</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>f</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>g</Rel>\
                                                </Atom>\
                                        </And>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>p</Rel>\
                                                <Expr>\
                                                        <Fun>f</Fun>\
                                                        <Data iso:type=\"symbol\">a</Data>\
                                                        <Data iso:type=\"number\">1</Data>\
                                                </Expr>\
                                                <Data iso:type=\"symbol\">b</Data>\
                                                <Data iso:type=\"symbol\">c</Data>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(36,
     [((term_0(a,1.2,"strings may contain \"") = term_1) :- (a, f, g ; b, c), d, \+ p(f(a, 1),b,c))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Equal>\
                                <Expr>\
                                        <Fun>term_0</Fun>\
                                        <Data iso:type=\"symbol\">a</Data>\
                                        <Data iso:type=\"number\">1.2</Data>\
                                        <Data iso:type=\"string\">\"strings may contain \\\"\"</Data>\
                                </Expr>\
                                <Expr>\
                                        <Fun>term_1</Fun>\
                                </Expr>\
                        </Equal>\
                </then>\
                <if>\
                        <And>\
                                <Or>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>a</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>f</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>g</Rel>\
                                                </Atom>\
                                        </And>\
                                        <And>\
                                                <Atom>\
                                                        <Rel>b</Rel>\
                                                </Atom>\
                                                <Atom>\
                                                        <Rel>c</Rel>\
                                                </Atom>\
                                        </And>\
                                </Or>\
                                <Atom>\
                                        <Rel>d</Rel>\
                                </Atom>\
                                <Naf>\
                                        <Atom>\
                                                <Rel>p</Rel>\
                                                <Expr>\
                                                        <Fun>f</Fun>\
                                                        <Data iso:type=\"symbol\">a</Data>\
                                                        <Data iso:type=\"number\">1</Data>\
                                                </Expr>\
                                                <Data iso:type=\"symbol\">b</Data>\
                                                <Data iso:type=\"symbol\">c</Data>\
                                        </Atom>\
                                </Naf>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(37,
     [(factorial(n) = mul(n, factorial(sub(n,1))) :- greaterThan(n, 0))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Equal>\
                                <Expr>\
                                        <Fun>factorial</Fun>\
                                        <Data iso:type=\"symbol\">n</Data>\
                                </Expr>\
                                <Expr>\
                                        <Fun>mul</Fun>\
                                        <Data iso:type=\"symbol\">n</Data>\
                                        <Expr>\
                                                <Fun>factorial</Fun>\
                                                <Expr>\
                                                        <Fun>sub</Fun>\
                                                        <Data iso:type=\"symbol\">n</Data>\
                                                        <Data iso:type=\"number\">1</Data>\
                                                </Expr>\
                                        </Expr>\
                                </Expr>\
                        </Equal>\
                </then>\
                <if>\
                        <Atom>\
                                <Rel>greaterThan</Rel>\
                                <Data iso:type=\"symbol\">n</Data>\
                                <Data iso:type=\"number\">0</Data>\
                        </Atom>\
                </if>\
        </Implies>\
     </Assert>").

test(38,
     [],
     [(?- p)],
     "<Query closure=\"existential\">\
        <Atom>\
                <Rel>p</Rel>\
        </Atom>\
      </Query>").

test(39,
     [],
     [(?- p(with, args))],
     "<Query closure=\"existential\">\
        <Atom>\
                <Rel>p</Rel>\
                <Data iso:type=\"symbol\">with</Data>\
                <Data iso:type=\"symbol\">args</Data>\
        </Atom>\
      </Query>").

test(40,
     [],
     [(?- p(h, f(g(a, 1))))],
     "<Query closure=\"existential\">\
        <Atom>\
                <Rel>p</Rel>\
                <Data iso:type=\"symbol\">h</Data>\
                <Expr>\
                        <Fun>f</Fun>\
                        <Expr>\
                                <Fun>g</Fun>\
                                <Data iso:type=\"symbol\">a</Data>\
                                <Data iso:type=\"number\">1</Data>\
                        </Expr>\
                </Expr>\
        </Atom>\
     </Query>").

test(41,
     [],
     [(?- p, q, r(1), s(-2.222342432), t("attached"))],
     "<Query closure=\"existential\">\
        <And>\
                <Atom>\
                        <Rel>p</Rel>\
                </Atom>\
                <Atom>\
                        <Rel>q</Rel>\
                </Atom>\
                <Atom>\
                        <Rel>r</Rel>\
                        <Data iso:type=\"number\">1</Data>\
                </Atom>\
                <Atom>\
                        <Rel>s</Rel>\
                        <Data iso:type=\"number\">-2.222342432</Data>\
                </Atom>\
                <Atom>\
                        <Rel>t</Rel>\
                        <Data iso:type=\"string\">\"attached\"</Data>\
                </Atom>\
        </And>\
      </Query>").

test(42,
     [a(item), b(item), c(item)],
     [(?- p, q, r(1), s(-2.222342432), t("attached")), (?- u, v('$V'(q)))],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>a</Rel>\
                <Data iso:type=\"symbol\">item</Data>\
        </Atom>\
        <Atom>\
                <Rel>b</Rel>\
                <Data iso:type=\"symbol\">item</Data>\
        </Atom>\
        <Atom>\
                <Rel>c</Rel>\
                <Data iso:type=\"symbol\">item</Data>\
        </Atom>\
     </Assert>\
     <Query closure=\"existential\">\
        <And>\
                <Atom>\
                        <Rel>p</Rel>\
                </Atom>\
                <Atom>\
                        <Rel>q</Rel>\
                </Atom>\
                <Atom>\
                        <Rel>r</Rel>\
                        <Data iso:type=\"number\">1</Data>\
                </Atom>\
                <Atom>\
                        <Rel>s</Rel>\
                        <Data iso:type=\"number\">-2.222342432</Data>\
                </Atom>\
                <Atom>\
                        <Rel>t</Rel>\
                        <Data iso:type=\"string\">\"attached\"</Data>\
                </Atom>\
        </And>\
     </Query>\
     <Query closure=\"existential\">\
        <And>\
                <Atom>\
                        <Rel>u</Rel>\
                </Atom>\
                <Atom>\
                        <Rel>v</Rel>\
                        <Var>q</Var>\
                </Atom>\
        </And>\
     </Query>").

test(43,
     [f([items,in,a,list])],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>f</Rel>\
                <Plex>\
                        <Data iso:type=\"symbol\">items</Data>\
                        <Data iso:type=\"symbol\">in</Data>\
                        <Data iso:type=\"symbol\">a</Data>\
                        <Data iso:type=\"symbol\">list</Data>\
                </Plex>\
        </Atom>\
     </Assert>").

test(44,
     [f([items,in,a,list|'$V'(x)])],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>f</Rel>\
                <Plex>\
                        <Data iso:type=\"symbol\">items</Data>\
                        <Data iso:type=\"symbol\">in</Data>\
                        <Data iso:type=\"symbol\">a</Data>\
                        <Data iso:type=\"symbol\">list</Data>\
                        <repo>\
                                <Var>x</Var>\
                        </repo>\
                </Plex>\
        </Atom>\
     </Assert>").

test(45,
     [select('$V'(x), ['$V'(x) | '$V'(xs)], '$V'(xs)),
      (select('$V'(x), ['$V'(y) | '$V'(xs)], ['$V'(y) | '$V'(ys)]) :- select('$V'(x), '$V'(xs), '$V'(ys)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>select</Rel>\
                <Var>x</Var>\
                <Plex>\
                        <Var>x</Var>\
                        <repo>\
                                <Var>xs</Var>\
                        </repo>\
                </Plex>\
                <Var>xs</Var>\
        </Atom>\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>select</Rel>\
                                <Var>x</Var>\
                                <Plex>\
                                        <Var>y</Var>\
                                        <repo>\
                                                <Var>xs</Var>\
                                        </repo>\
                                </Plex>\
                                <Plex>\
                                        <Var>y</Var>\
                                        <repo>\
                                                <Var>ys</Var>\
                                        </repo>\
                                </Plex>\
                        </Atom>\
                </then>\
                <if>\
                        <Atom>\
                                <Rel>select</Rel>\
                                <Var>x</Var>\
                                <Var>xs</Var>\
                                <Var>ys</Var>\
                        </Atom>\
                </if>\
        </Implies>\
     </Assert>").

test(46,
     [permutation([], []),
      (permutation(['$V'(x) | '$V'(xs)], '$V'(ys)) :-
           permutation('$V'(xs), '$V'(yss)), select('$V'(x), '$V'(ys), '$V'(yss)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>permutation</Rel>\
                <Plex/>\
                <Plex/>\
        </Atom>\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>permutation</Rel>\
                                <Plex>\
                                        <Var>x</Var>\
                                        <repo>\
                                                <Var>xs</Var>\
                                        </repo>\
                                </Plex>\
                                <Var>ys</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>permutation</Rel>\
                                        <Var>xs</Var>\
                                        <Var>yss</Var>\
                                </Atom>\
                                <Atom>\
                                        <Rel>select</Rel>\
                                        <Var>x</Var>\
                                        <Var>ys</Var>\
                                        <Var>yss</Var>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

%% Try a more substantial test case.
test(47,
     [(runwayOneOrientation('$V'(runOneOr)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayTwoOrientation('$V'(runTwoOr)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayThreeOrientation('$V'(runThreeOr)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayFourOrientation('$V'(runFourOr)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayOneName('$V'(runOneName)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayTwoName('$V'(runTwoName)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayThreeName('$V'(runThreeName)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (runwayFourName('$V'(runFourName)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code))),
      (distanceBetweenRunways('$V'(distanceBetweenRunways)) :- airportChar('$V'(code), '$V'(runOneOr), '$V'(runTwoOr), '$V'(runThreeOr), '$V'(runFourOr), '$V'(runOneName), '$V'(runTwoName), '$V'(runThreeName), '$V'(runFourName), '$V'(distanceBetweenRunways), '$V'(rules)), airportName('$V'(code)))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayOneOrientation</Rel>\
                    <Var>runOneOr</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayTwoOrientation</Rel>\
                    <Var>runTwoOr</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayThreeOrientation</Rel>\
                    <Var>runThreeOr</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayFourOrientation</Rel>\
                    <Var>runFourOr</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayOneName</Rel>\
                    <Var>runOneName</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayTwoName</Rel>\
                    <Var>runTwoName</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayThreeName</Rel>\
                    <Var>runThreeName</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>runwayFourName</Rel>\
                    <Var>runFourName</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>distanceBetweenRunways</Rel>\
                    <Var>distanceBetweenRunways</Var>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>airportChar</Rel>\
                        <Var>code</Var>\
                        <Var>runOneOr</Var>\
                        <Var>runTwoOr</Var>\
                        <Var>runThreeOr</Var>\
                        <Var>runFourOr</Var>\
                        <Var>runOneName</Var>\
                        <Var>runTwoName</Var>\
                        <Var>runThreeName</Var>\
                        <Var>runFourName</Var>\
                        <Var>distanceBetweenRunways</Var>\
                        <Var>rules</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>airportName</Rel>\
                        <Var>code</Var>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
    </Assert>").

test(48,
     [(icaoCategory('$V'(aircraft), light) :- aircraftChar(['$V'(aircraft), '$V'(kg) | '$V'(rest)]), lessThanOrEqual('$V'(kg), 7000.0)),
      (icaoCategory('$V'(aircraft), medium):- aircraftChar(['$V'(aircraft), '$V'(kg) | '$V'(rest)]), lessThan('$V'(kg), 136000.0), greaterThan('$V'(kg), 7000.0)),
      (icaoCategory('$V'(aircraft), heavy) :- aircraftChar(['$V'(aircraft), '$V'(kg) | '$V'(rest)]), greaterThanOrEqual('$V'(kg), 136000.0), \+ icaoCategory('$V'(aircraft), super)),
      (icaoCategoryPreceding(light) :- mtowPreceding('$V'(kgPreceding)), lessThanOrEqual('$V'(kgPreceding), 7000.0)),
      (icaoCategoryPreceding(medium) :-  mtowPreceding('$V'(kgPreceding)), lessThan('$V'(kgPreceding), 136000.0), greaterThan('$V'(kgPreceding), 7000.0)),
      (icaoCategoryPreceding(heavy) :- precedingAircraftType('$V'(modelPreceding)), notEqual('$V'(modelPreceding),'A388'), notEqual('$V'(modelPreceding),'A38F'), notEqual('$V'(modelPreceding),'A225'), mtowPreceding('$V'(kgPreceding)), greaterThanOrEqual('$V'(kgPreceding), 136000.0)),

      (icaoCategoryPreceding(super) :- precedingAircraftType('A388')),
      (icaoCategoryPreceding(super) :- precedingAircraftType('A38F')),

      (icaoSeparationMiles(4):- icaoCategory(heavy), icaoCategoryPreceding(heavy)),
      (icaoSeparationMiles(5):- icaoCategory(medium), icaoCategoryPreceding(heavy)),
      (icaoSeparationMiles(6):- icaoCategory(light), icaoCategoryPreceding(heavy)),
      (icaoSeparationMiles(5):- icaoCategory(light), icaoCategoryPreceding(medium)),
      (icaoSeparationMiles(mrs):- icaoCategoryPreceding(light)),
      (icaoSeparationMiles(mrs):- icaoCategory(medium), icaoCategoryPreceding(medium)),
      (icaoSeparationMiles(mrs):- icaoCategory(heavy), icaoCategoryPreceding(medium)),
      (icaoSeparationMiles(mrs):- icaoCategory(super)),
      (icaoSeparationMiles(6):- icaoCategory(heavy), icaoCategoryPreceding(super)),
      (icaoSeparationMiles(7):- icaoCategory(medium), icaoCategoryPreceding(super)),
      (icaoSeparationMiles(8):- icaoCategory(light), icaoCategoryPreceding(super))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategory</Rel>\
                    <Var>aircraft</Var>\
                    <Data iso:type=\"symbol\">light</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>aircraftChar</Rel>\
                        <Plex>\
                            <Var>aircraft</Var>\
                            <Var>kg</Var>\
                            <repo>\
                                <Var>rest</Var>\
                            </repo>\
                        </Plex>\
                    </Atom>\
                    <Atom>\
                        <Rel>lessThanOrEqual</Rel>\
                        <Var>kg</Var>\
                        <Data iso:type=\"number\">7000.0</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategory</Rel>\
                    <Var>aircraft</Var>\
                    <Data iso:type=\"symbol\">medium</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>aircraftChar</Rel>\
                        <Plex>\
                            <Var>aircraft</Var>\
                            <Var>kg</Var>\
                            <repo>\
                                <Var>rest</Var>\
                            </repo>\
                        </Plex>\
                    </Atom>\
                    <Atom>\
                        <Rel>lessThan</Rel>\
                        <Var>kg</Var>\
                        <Data iso:type=\"number\">136000.0</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>greaterThan</Rel>\
                        <Var>kg</Var>\
                        <Data iso:type=\"number\">7000.0</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategory</Rel>\
                    <Var>aircraft</Var>\
                    <Data iso:type=\"symbol\">heavy</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>aircraftChar</Rel>\
                        <Plex>\
                            <Var>aircraft</Var>\
                            <Var>kg</Var>\
                            <repo>\
                                <Var>rest</Var>\
                            </repo>\
                        </Plex>\
                    </Atom>\
                    <Atom>\
                        <Rel>greaterThanOrEqual</Rel>\
                        <Var>kg</Var>\
                        <Data iso:type=\"number\">136000.0</Data>\
                    </Atom>\
                    <Naf>\
                        <Atom>\
                            <Rel>icaoCategory</Rel>\
                            <Var>aircraft</Var>\
                            <Data iso:type=\"symbol\">super</Data>\
                        </Atom>\
                    </Naf>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategoryPreceding</Rel>\
                    <Data iso:type=\"symbol\">light</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>mtowPreceding</Rel>\
                        <Var>kgPreceding</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>lessThanOrEqual</Rel>\
                        <Var>kgPreceding</Var>\
                        <Data iso:type=\"number\">7000.0</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategoryPreceding</Rel>\
                    <Data iso:type=\"symbol\">medium</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>mtowPreceding</Rel>\
                        <Var>kgPreceding</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>lessThan</Rel>\
                        <Var>kgPreceding</Var>\
                        <Data iso:type=\"number\">136000.0</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>greaterThan</Rel>\
                        <Var>kgPreceding</Var>\
                        <Data iso:type=\"number\">7000.0</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategoryPreceding</Rel>\
                    <Data iso:type=\"symbol\">heavy</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>precedingAircraftType</Rel>\
                        <Var>modelPreceding</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>notEqual</Rel>\
                        <Var>modelPreceding</Var>\
                        <Ind>A388</Ind>\
                    </Atom>\
                    <Atom>\
                        <Rel>notEqual</Rel>\
                        <Var>modelPreceding</Var>\
                        <Ind>A38F</Ind>\
                    </Atom>\
                    <Atom>\
                        <Rel>notEqual</Rel>\
                        <Var>modelPreceding</Var>\
                        <Ind>A225</Ind>\
                    </Atom>\
                    <Atom>\
                        <Rel>mtowPreceding</Rel>\
                        <Var>kgPreceding</Var>\
                    </Atom>\
                    <Atom>\
                        <Rel>greaterThanOrEqual</Rel>\
                        <Var>kgPreceding</Var>\
                        <Data iso:type=\"number\">136000.0</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategoryPreceding</Rel>\
                    <Data iso:type=\"symbol\">super</Data>\
                </Atom>\
            </then>\
            <if>\
                <Atom>\
                    <Rel>precedingAircraftType</Rel>\
                    <Ind>A388</Ind>\
                </Atom>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoCategoryPreceding</Rel>\
                    <Data iso:type=\"symbol\">super</Data>\
                </Atom>\
            </then>\
            <if>\
                <Atom>\
                    <Rel>precedingAircraftType</Rel>\
                    <Ind>A38F</Ind>\
                </Atom>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">4</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">heavy</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">heavy</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">5</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">medium</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">heavy</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">6</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">light</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">heavy</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">5</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">light</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">medium</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"symbol\">mrs</Data>\
                </Atom>\
            </then>\
            <if>\
                <Atom>\
                    <Rel>icaoCategoryPreceding</Rel>\
                    <Data iso:type=\"symbol\">light</Data>\
                </Atom>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"symbol\">mrs</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">medium</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">medium</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"symbol\">mrs</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">heavy</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">medium</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"symbol\">mrs</Data>\
                </Atom>\
            </then>\
            <if>\
                <Atom>\
                    <Rel>icaoCategory</Rel>\
                    <Data iso:type=\"symbol\">super</Data>\
                </Atom>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">6</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">heavy</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">super</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">7</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">medium</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">super</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
        <Implies>\
            <then>\
                <Atom>\
                    <Rel>icaoSeparationMiles</Rel>\
                    <Data iso:type=\"number\">8</Data>\
                </Atom>\
            </then>\
            <if>\
                <And>\
                    <Atom>\
                        <Rel>icaoCategory</Rel>\
                        <Data iso:type=\"symbol\">light</Data>\
                    </Atom>\
                    <Atom>\
                        <Rel>icaoCategoryPreceding</Rel>\
                        <Data iso:type=\"symbol\">super</Data>\
                    </Atom>\
                </And>\
            </if>\
        </Implies>\
    </Assert>").

test(49,
     [(aircraftChar('A500',3175.144,44.0,97.5)),
      (aircraftChar('SGUP',77110.64,156.25,123.0)),
      (aircraftChar('AR11',566.99,36.0,64.0)),
      (aircraftChar('AR15',929.8636,37.5,67.0)),
      (aircraftChar('AT43',16699.896664,80.58,124.0)),
      (aircraftChar('AT45',18599.53996,80.6,128.0)),
      (aircraftChar('AT72',21999.665592,88.75,128.0)),
      (aircraftChar('N262',10800.02552,74.17,96.0)),
      (aircraftChar('S210',49985.8384,112.5,127.0)),
      (aircraftChar('S601',6599.7636,42.25,118.0)),
      (aircraftChar('AEST',2864.43348,36.7,94.0)),
      (aircraftChar('AEST',2721.552,36.71,94.0)),
      (aircraftChar('AEST',2721.552,36.71,94.0)),
      (aircraftChar('AT3P',1583.943264,45.15,76.0)),
      (aircraftChar('AT3T',4159.43864,51.0,69.0)),
      (aircraftChar('AT5T',2902.9888,52.0,69.0)),
      (aircraftChar('AT6T',5669.9,56.0,78.0)),
      (aircraftChar('AT8T',7257.472,52.1,82.0)),
      (aircraftChar('A306',164998.62592,147.08,132.0)),
      (aircraftChar('A3ST',140613.52,147.17,135.0)),
      (aircraftChar('A30B',141999.24356,147.08,131.0)),
      (aircraftChar('A30B',171684.572,147.08,135.0)),
      (aircraftChar('A310',164018.8672,144.0,135.0)),
      (aircraftChar('A310',149999.699256,144.1,125.0)),
      (aircraftChar('A318',59000.9794,111.9,138.0)),
      (aircraftChar('A319',63999.56324,111.3,138.0)),
      (aircraftChar('A320',65999.90396,111.3,138.0)),
      (aircraftChar('A320',73500.04768,111.3,138.0)),
      (aircraftChar('A321',93439.952,111.83,138.0)),
      (aircraftChar('A388',560186.12,261.3,145.0)),
      (aircraftChar('A38F',590032.4736,261.65,145.0)),
      (aircraftChar('AA1',680.388,24.5,70.0)),
      (aircraftChar('AA5',997.9024,31.5,80.0)),
      (aircraftChar('CH7A',598.74144,33.5,78.0)),
      (aircraftChar('CH7A',793.786,33.5,88.0)),
      (aircraftChar('CH7B',816.4656,34.5,87.0)),
      (aircraftChar('BL8',975.2228,36.2,92.0)),
      (aircraftChar('BL8',884.5044,32.0,90.0)),
      (aircraftChar('AN12',55111.428,124.8,127.0)),
      (aircraftChar('A124',404999.142632,240.5,124.0)),
      (aircraftChar('A140',21500.2608,83.67,230.0)),
      (aircraftChar('AN72',29937.072,84.7,89.0)),
      (aircraftChar('AT72',19989.79944,88.09,105.0)),
      (aircraftChar('AT43',15172.6524,58.02,103.0)),
      (aircraftChar('AT43',16699.896664,80.58,104.0)),
      (aircraftChar('AT44',16150.14316,80.58,105.0)),
      (aircraftChar('AT45',16150.14316,80.42,105.0)),
      (aircraftChar('AT72',21500.2608,88.75,105.0)),
      (aircraftChar('AT72',19989.79944,88.75,105.0)),
      (aircraftChar('BA11',35833.768,88.5,129.0)),
      (aircraftChar('BA11',40142.892,88.5,137.0)),
      (aircraftChar('B461',38101.728,86.42,113.0)),
      (aircraftChar('B462',42184.056,86.42,117.0)),
      (aircraftChar('B463',44225.22,86.42,121.0)),
      (aircraftChar('BE18',4490.5608,49.67,87.0)),
      (aircraftChar('BE24',1247.378,38.6666666667,70.0)),
      (aircraftChar('BE55',2404.0376,37.83,88.0)),
      (aircraftChar('B190',7765.49504,58.0,113.0)),
      (aircraftChar('BE99',5125.5896,45.92,107.0)),
      (aircraftChar('B190',7529.6272,54.5,113.0)),
      (aircraftChar('BE58',2494.756,37.8,96.0)),
      (aircraftChar('BE58',2812.2704,37.8,101.0)),
      (aircraftChar('BE58',2812.2704,37.8,101.0)),
      (aircraftChar('BE36',1655.6108,33.5,80.0)),
      (aircraftChar('BE36',1746.3292,37.83,75.0)),
      (aircraftChar('BE35',1542.2128,33.5,70.0)),
      (aircraftChar('BE76',1769.0088,38.0,76.0)),
      (aircraftChar('BE60',3050.4062,39.25,98.0)),
      (aircraftChar('BE10',5352.3856,45.92,111.0)),
      (aircraftChar('BE9L',4581.2792,50.25,100.0)),
      (aircraftChar('BE9T',4966.8324,45.9,108.0)),
      (aircraftChar('PRM1',5669.9,44.5,108.0)),
      (aircraftChar('BE77',759.7666,30.0,63.0)),
      (aircraftChar('BE23',1111.3004,32.75,68.0)),
      (aircraftChar('BE20',5669.9,54.5,103.0)),
      (aircraftChar('B720',104008.6456,130.83,133.0)),
      (aircraftChar('B742',377842.136,195.67,152.0)),
      (aircraftChar('B74S',317514.4,195.67,140.0)),
      (aircraftChar('B74R',272155.2,195.7,141.0)),
      (aircraftChar('B752',115665.96,124.67,135.0)),
      (aircraftChar('B752',99790.24,124.83,135.0)),
      (aircraftChar('B772',347451.472,212.07,145.0)),
      (aircraftChar('B773',340194.0,212.07,145.0)),
      (aircraftChar('B701',116727.36528,130.83,139.0)),
      (aircraftChar('B703',141520.704,142.42,139.0)),
      (aircraftChar('B703',151318.2912,145.75,136.0)),
      (aircraftChar('B712',54884.632,93.3333333333,125.0)),
      (aircraftChar('B720',106276.6056,130.83,137.0)),
      (aircraftChar('B721',76657.048,108.0,125.0)),
      (aircraftChar('B722',95027.524,108.0,138.0)),
      (aircraftChar('B731',49895.12,94.0,137.0)),
      (aircraftChar('B732',52389.876,93.0,137.0)),
      (aircraftChar('B733',63276.084,94.75,135.0)),
      (aircraftChar('B734',68038.8,94.75,139.0)),
      (aircraftChar('B735',61688.512,94.75,140.0)),
      (aircraftChar('B736',65997.636,112.58,125.0)),
      (aircraftChar('B737',70079.964,112.58,130.0)),
      (aircraftChar('B738',79015.7264,112.58,141.0)),
      (aircraftChar('B739',74389.088,112.07,144.0)),
      (aircraftChar('B744',394625.04,213.0,154.0)),
      (aircraftChar('B753',123603.82,124.83,142.0)),
      (aircraftChar('B762',142881.48,156.08,130.0)),
      (aircraftChar('B753',158757.2,156.08,130.0)),
      (aircraftChar('B772',286896.94,199.9,145.0)),
      (aircraftChar('B773',299370.72,199.9,145.0)),
      (aircraftChar('B52',221352.896,185.0,141.0)),
      (aircraftChar('C97',66133.7136,141.3,105.0)),
      (aircraftChar('NOMA',4059.6484,54.0,69.0)),
      (aircraftChar('GLEX',43091.24,94.0,126.0)),
      (aircraftChar('CL60',21590.9792,61.8,125.0)),
      (aircraftChar('TRIS',4535.92,53.0,65.0)),
      (aircraftChar('CL60',18710.67,61.8,125.0)),
      (aircraftChar('CL44',95254.32,142.3,123.0)),
      (aircraftChar('C207',16510.7488,91.2,102.0)),
      (aircraftChar('C150',725.7472,33.5,55.0)),
      (aircraftChar('C177',1133.98,35.5,64.0)),
      (aircraftChar('C182',1406.1352,36.0,92.0)),
      (aircraftChar('C206',1632.9312,36.0,92.0)),
      (aircraftChar('C402',2857.6296,44.17,95.0)),
      (aircraftChar('C402',2857.6296,44.17,95.0)),
      (aircraftChar('C404',3810.1728,46.3,92.0)),
      (aircraftChar('C414',3077.62172,44.1,94.0)),
      (aircraftChar('C421',3379.2604,41.7,96.0)),
      (aircraftChar('C421',3102.56928,41.7,96.0)),
      (aircraftChar('C441',4501.9006,49.3,100.0)),
      (aircraftChar('C208',3628.736,52.1,104.0)),
      (aircraftChar('A37_',6350.288,35.92,131.0)),
      (aircraftChar('C550',6713.1616,52.17,112.0)),
      (aircraftChar('C525',4808.0752,46.8,107.0)),
      (aircraftChar('C25A',5669.9,49.83,118.0)),
      (aircraftChar('C560',7543.23496,54.08,108.0)),
      (aircraftChar('C500',5375.0652,47.1,108.0)),
      (aircraftChar('C550',6032.7736,51.7,108.0)),
      (aircraftChar('C650',9979.024,53.5,114.0)),
      (aircraftChar('C560',7633.95336,55.8,107.0)),
      (aircraftChar('CVLP',18955.60968,91.8,107.0)),
      (aircraftChar('CVLP',22543.5224,105.33,104.0)),
      (aircraftChar('CVLP',22543.5224,105.33,106.0)),
      (aircraftChar('CVLT',24766.1232,105.3,107.0)),
      (aircraftChar('FA20',18497.48176,61.92,113.0)),
      (aircraftChar('F900',20638.436,63.42,100.0)),
      (aircraftChar('F2TH',16238.5936,63.33,114.0)),
      (aircraftChar('ATLA',43500.379984,119.08,130.0)),
      (aircraftChar('FA10',8300.7336,42.92,104.0)),
      (aircraftChar('FA20',12999.94672,53.5,107.0)),
      (aircraftChar('DOVE',4059.6484,57.0,84.0)),
      (aircraftChar('HERN',6123.492,71.5,85.0)),
      (aircraftChar('DH2T',2313.3192,48.0,50.0)),
      (aircraftChar('DHC4',12927.372,95.67,77.0)),
      (aircraftChar('DHC6',5669.9,65.0,75.0)),
      (aircraftChar('DHC7',19958.048,93.0,83.0)),
      (aircraftChar('DH8C',18642.6312,90.0,90.0)),
      (aircraftChar('E110',5899.871144,50.3,92.0)),
      (aircraftChar('E121',5669.9,47.4,92.0)),
      (aircraftChar('PA31',3175.144,40.5833333333,74.0)),
      (aircraftChar('D28D',4016.55716,51.0,74.0)),
      (aircraftChar('A10_',23133.192,57.5,140.0)),
      (aircraftChar('VF14',19958.048,70.5,111.0)),
      (aircraftChar('LJ25',6803.88,35.6,137.0)),
      (aircraftChar('LJ24',5896.696,35.6,128.0)),
      (aircraftChar('LJ25',6803.88,35.6,137.0)),
      (aircraftChar('LJ28',6803.88,43.7,120.0)),
      (aircraftChar('LJ28',8300.7336,39.5,143.0)),
      (aircraftChar('GLF2',29619.5576,68.1,141.0)),
      (aircraftChar('GLF3',31161.7704,77.1,136.0)),
      (aircraftChar('GLF4',33837.9632,77.1,149.0)),
      (aircraftChar('GLF4',33202.9344,77.1,128.0)),
      (aircraftChar('GLF5',41276.872,93.5,145.0)),
      (aircraftChar('A748',21092.028,102.46,94.0)),
      (aircraftChar('TRID',71667.536,98.0,146.0)),
      (aircraftChar('A748',22679.6,98.2,100.0)),
      (aircraftChar('WW23',10659.412,44.8,129.0)),
      (aircraftChar('ASTR',11181.0428,54.7,126.0)),
      (aircraftChar('ARVA',6803.88,68.8,81.0)),
      (aircraftChar('ARVA',6803.88,68.8,81.0)),
      (aircraftChar('JCOM',7620.3456,43.3,130.0)),
      (aircraftChar('WW24',10659.412,44.8,129.0)),
      (aircraftChar('WW24',10659.412,44.8,129.0)),
      (aircraftChar('IL18',61071.62688,122.7,103.0)),
      (aircraftChar('IL76',169999.47772,165.7,119.0)),
      (aircraftChar('C130',70306.76,132.07,129.0)),
      (aircraftChar('C130',70306.76,132.6,129.0)),
      (aircraftChar('C130',70306.76,132.07,138.0)),
      (aircraftChar('C130',70306.76,132.6,138.0)),
      (aircraftChar('L101',195044.56,155.3,138.0)),
      (aircraftChar('L101',211373.872,155.3,140.0)),
      (aircraftChar('L101',211373.872,155.3,144.0)),
      (aircraftChar('L101',231331.92,155.3,144.0)),
      (aircraftChar('L101',234053.472,155.3,148.0)),
      (aircraftChar('L29A',19844.65,54.4,132.0)),
      (aircraftChar('C141',143607.2272,159.9,129.0)),
      (aircraftChar('C141',155582.056,159.9,129.0)),
      (aircraftChar('C5',348812.248,222.7,135.0)),
      (aircraftChar('C5',379656.504,222.7,135.0)),
      (aircraftChar('P3',61234.92,99.7,134.0)),
      (aircraftChar('A4_',11113.004,27.5,120.0)),
      (aircraftChar('DC10',200941.256,155.3,136.0)),
      (aircraftChar('DC7',64863.656,127.5,110.0)),
      (aircraftChar('DC85',147417.4,142.4,137.0)),
      (aircraftChar('MD11',273289.18,169.8,155.0)),
      (aircraftChar('BE40',7135.00216,43.5,100.0)),
      (aircraftChar('MU2',5250.3274,39.1666666667,88.0)),
      (aircraftChar('MU2',4898.7936,39.2,119.0)),
      (aircraftChar('B2',152633.708,172.0,140.0)),
      (aircraftChar('AEST',2864.43348,36.67,94.0)),
      (aircraftChar('PA31',2812.2704,40.7,100.0)),
      (aircraftChar('PAY4',5465.7836,47.7,110.0)),
      (aircraftChar('AN2',5499.803,59.67,54.0)),
      (aircraftChar('BE40',7302.8312,43.06,111.0)),
      (aircraftChar('AC11',5216.308,46.0,75.0)),
      (aircraftChar('AC95',4683.3374,52.2,121.0)),
      (aircraftChar('AC50',3061.746,49.08,97.0)),
      (aircraftChar('AC56',2948.348,49.0833333333,97.0)),
      (aircraftChar('AC68',3401.94,49.0833333333,97.0)),
      (aircraftChar('B1_',216363.384,137.0,165.0)),
      (aircraftChar('AC52',2494.756,44.1,97.0)),
      (aircraftChar('AC80',4059.6484,49.05,97.0)),
      (aircraftChar('AC90',4649.318,46.67,97.0)),
      (aircraftChar('SBR1',8459.4908,44.5,120.0)),
      (aircraftChar('SBR1',9071.84,44.5,120.0)),
      (aircraftChar('SBR1',10886.208,50.5,105.0)),
      (aircraftChar('SBR2',10568.6936,44.5,137.0)),
      (aircraftChar('SBR2',11113.004,50.4,128.0)),
      (aircraftChar('SH33',9979.024,74.67,96.0)),
      (aircraftChar('SH36',11793.392,74.8,104.0))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A500</Ind>\
                <Data iso:type=\"number\">3175.144</Data>\
                <Data iso:type=\"number\">44.0</Data>\
                <Data iso:type=\"number\">97.5</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SGUP</Ind>\
                <Data iso:type=\"number\">77110.64</Data>\
                <Data iso:type=\"number\">156.25</Data>\
                <Data iso:type=\"number\">123.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AR11</Ind>\
                <Data iso:type=\"number\">566.99</Data>\
                <Data iso:type=\"number\">36.0</Data>\
                <Data iso:type=\"number\">64.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AR15</Ind>\
                <Data iso:type=\"number\">929.8636</Data>\
                <Data iso:type=\"number\">37.5</Data>\
                <Data iso:type=\"number\">67.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT43</Ind>\
                <Data iso:type=\"number\">16699.896664</Data>\
                <Data iso:type=\"number\">80.58</Data>\
                <Data iso:type=\"number\">124.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT45</Ind>\
                <Data iso:type=\"number\">18599.53996</Data>\
                <Data iso:type=\"number\">80.6</Data>\
                <Data iso:type=\"number\">128.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT72</Ind>\
                <Data iso:type=\"number\">21999.665592</Data>\
                <Data iso:type=\"number\">88.75</Data>\
                <Data iso:type=\"number\">128.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>N262</Ind>\
                <Data iso:type=\"number\">10800.02552</Data>\
                <Data iso:type=\"number\">74.17</Data>\
                <Data iso:type=\"number\">96.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>S210</Ind>\
                <Data iso:type=\"number\">49985.8384</Data>\
                <Data iso:type=\"number\">112.5</Data>\
                <Data iso:type=\"number\">127.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>S601</Ind>\
                <Data iso:type=\"number\">6599.7636</Data>\
                <Data iso:type=\"number\">42.25</Data>\
                <Data iso:type=\"number\">118.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AEST</Ind>\
                <Data iso:type=\"number\">2864.43348</Data>\
                <Data iso:type=\"number\">36.7</Data>\
                <Data iso:type=\"number\">94.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AEST</Ind>\
                <Data iso:type=\"number\">2721.552</Data>\
                <Data iso:type=\"number\">36.71</Data>\
                <Data iso:type=\"number\">94.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AEST</Ind>\
                <Data iso:type=\"number\">2721.552</Data>\
                <Data iso:type=\"number\">36.71</Data>\
                <Data iso:type=\"number\">94.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT3P</Ind>\
                <Data iso:type=\"number\">1583.943264</Data>\
                <Data iso:type=\"number\">45.15</Data>\
                <Data iso:type=\"number\">76.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT3T</Ind>\
                <Data iso:type=\"number\">4159.43864</Data>\
                <Data iso:type=\"number\">51.0</Data>\
                <Data iso:type=\"number\">69.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT5T</Ind>\
                <Data iso:type=\"number\">2902.9888</Data>\
                <Data iso:type=\"number\">52.0</Data>\
                <Data iso:type=\"number\">69.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT6T</Ind>\
                <Data iso:type=\"number\">5669.9</Data>\
                <Data iso:type=\"number\">56.0</Data>\
                <Data iso:type=\"number\">78.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT8T</Ind>\
                <Data iso:type=\"number\">7257.472</Data>\
                <Data iso:type=\"number\">52.1</Data>\
                <Data iso:type=\"number\">82.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A306</Ind>\
                <Data iso:type=\"number\">164998.62592</Data>\
                <Data iso:type=\"number\">147.08</Data>\
                <Data iso:type=\"number\">132.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A3ST</Ind>\
                <Data iso:type=\"number\">140613.52</Data>\
                <Data iso:type=\"number\">147.17</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A30B</Ind>\
                <Data iso:type=\"number\">141999.24356</Data>\
                <Data iso:type=\"number\">147.08</Data>\
                <Data iso:type=\"number\">131.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A30B</Ind>\
                <Data iso:type=\"number\">171684.572</Data>\
                <Data iso:type=\"number\">147.08</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A310</Ind>\
                <Data iso:type=\"number\">164018.8672</Data>\
                <Data iso:type=\"number\">144.0</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A310</Ind>\
                <Data iso:type=\"number\">149999.699256</Data>\
                <Data iso:type=\"number\">144.1</Data>\
                <Data iso:type=\"number\">125.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A318</Ind>\
                <Data iso:type=\"number\">59000.9794</Data>\
                <Data iso:type=\"number\">111.9</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A319</Ind>\
                <Data iso:type=\"number\">63999.56324</Data>\
                <Data iso:type=\"number\">111.3</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A320</Ind>\
                <Data iso:type=\"number\">65999.90396</Data>\
                <Data iso:type=\"number\">111.3</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A320</Ind>\
                <Data iso:type=\"number\">73500.04768</Data>\
                <Data iso:type=\"number\">111.3</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A321</Ind>\
                <Data iso:type=\"number\">93439.952</Data>\
                <Data iso:type=\"number\">111.83</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A388</Ind>\
                <Data iso:type=\"number\">560186.12</Data>\
                <Data iso:type=\"number\">261.3</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A38F</Ind>\
                <Data iso:type=\"number\">590032.4736</Data>\
                <Data iso:type=\"number\">261.65</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AA1</Ind>\
                <Data iso:type=\"number\">680.388</Data>\
                <Data iso:type=\"number\">24.5</Data>\
                <Data iso:type=\"number\">70.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AA5</Ind>\
                <Data iso:type=\"number\">997.9024</Data>\
                <Data iso:type=\"number\">31.5</Data>\
                <Data iso:type=\"number\">80.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CH7A</Ind>\
                <Data iso:type=\"number\">598.74144</Data>\
                <Data iso:type=\"number\">33.5</Data>\
                <Data iso:type=\"number\">78.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CH7A</Ind>\
                <Data iso:type=\"number\">793.786</Data>\
                <Data iso:type=\"number\">33.5</Data>\
                <Data iso:type=\"number\">88.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CH7B</Ind>\
                <Data iso:type=\"number\">816.4656</Data>\
                <Data iso:type=\"number\">34.5</Data>\
                <Data iso:type=\"number\">87.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BL8</Ind>\
                <Data iso:type=\"number\">975.2228</Data>\
                <Data iso:type=\"number\">36.2</Data>\
                <Data iso:type=\"number\">92.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BL8</Ind>\
                <Data iso:type=\"number\">884.5044</Data>\
                <Data iso:type=\"number\">32.0</Data>\
                <Data iso:type=\"number\">90.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AN12</Ind>\
                <Data iso:type=\"number\">55111.428</Data>\
                <Data iso:type=\"number\">124.8</Data>\
                <Data iso:type=\"number\">127.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A124</Ind>\
                <Data iso:type=\"number\">404999.142632</Data>\
                <Data iso:type=\"number\">240.5</Data>\
                <Data iso:type=\"number\">124.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A140</Ind>\
                <Data iso:type=\"number\">21500.2608</Data>\
                <Data iso:type=\"number\">83.67</Data>\
                <Data iso:type=\"number\">230.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AN72</Ind>\
                <Data iso:type=\"number\">29937.072</Data>\
                <Data iso:type=\"number\">84.7</Data>\
                <Data iso:type=\"number\">89.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT72</Ind>\
                <Data iso:type=\"number\">19989.79944</Data>\
                <Data iso:type=\"number\">88.09</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT43</Ind>\
                <Data iso:type=\"number\">15172.6524</Data>\
                <Data iso:type=\"number\">58.02</Data>\
                <Data iso:type=\"number\">103.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT43</Ind>\
                <Data iso:type=\"number\">16699.896664</Data>\
                <Data iso:type=\"number\">80.58</Data>\
                <Data iso:type=\"number\">104.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT44</Ind>\
                <Data iso:type=\"number\">16150.14316</Data>\
                <Data iso:type=\"number\">80.58</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT45</Ind>\
                <Data iso:type=\"number\">16150.14316</Data>\
                <Data iso:type=\"number\">80.42</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT72</Ind>\
                <Data iso:type=\"number\">21500.2608</Data>\
                <Data iso:type=\"number\">88.75</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AT72</Ind>\
                <Data iso:type=\"number\">19989.79944</Data>\
                <Data iso:type=\"number\">88.75</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BA11</Ind>\
                <Data iso:type=\"number\">35833.768</Data>\
                <Data iso:type=\"number\">88.5</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BA11</Ind>\
                <Data iso:type=\"number\">40142.892</Data>\
                <Data iso:type=\"number\">88.5</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B461</Ind>\
                <Data iso:type=\"number\">38101.728</Data>\
                <Data iso:type=\"number\">86.42</Data>\
                <Data iso:type=\"number\">113.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B462</Ind>\
                <Data iso:type=\"number\">42184.056</Data>\
                <Data iso:type=\"number\">86.42</Data>\
                <Data iso:type=\"number\">117.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B463</Ind>\
                <Data iso:type=\"number\">44225.22</Data>\
                <Data iso:type=\"number\">86.42</Data>\
                <Data iso:type=\"number\">121.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE18</Ind>\
                <Data iso:type=\"number\">4490.5608</Data>\
                <Data iso:type=\"number\">49.67</Data>\
                <Data iso:type=\"number\">87.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE24</Ind>\
                <Data iso:type=\"number\">1247.378</Data>\
                <Data iso:type=\"number\">38.6666666667</Data>\
                <Data iso:type=\"number\">70.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE55</Ind>\
                <Data iso:type=\"number\">2404.0376</Data>\
                <Data iso:type=\"number\">37.83</Data>\
                <Data iso:type=\"number\">88.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B190</Ind>\
                <Data iso:type=\"number\">7765.49504</Data>\
                <Data iso:type=\"number\">58.0</Data>\
                <Data iso:type=\"number\">113.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE99</Ind>\
                <Data iso:type=\"number\">5125.5896</Data>\
                <Data iso:type=\"number\">45.92</Data>\
                <Data iso:type=\"number\">107.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B190</Ind>\
                <Data iso:type=\"number\">7529.6272</Data>\
                <Data iso:type=\"number\">54.5</Data>\
                <Data iso:type=\"number\">113.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE58</Ind>\
                <Data iso:type=\"number\">2494.756</Data>\
                <Data iso:type=\"number\">37.8</Data>\
                <Data iso:type=\"number\">96.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE58</Ind>\
                <Data iso:type=\"number\">2812.2704</Data>\
                <Data iso:type=\"number\">37.8</Data>\
                <Data iso:type=\"number\">101.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE58</Ind>\
                <Data iso:type=\"number\">2812.2704</Data>\
                <Data iso:type=\"number\">37.8</Data>\
                <Data iso:type=\"number\">101.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE36</Ind>\
                <Data iso:type=\"number\">1655.6108</Data>\
                <Data iso:type=\"number\">33.5</Data>\
                <Data iso:type=\"number\">80.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE36</Ind>\
                <Data iso:type=\"number\">1746.3292</Data>\
                <Data iso:type=\"number\">37.83</Data>\
                <Data iso:type=\"number\">75.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE35</Ind>\
                <Data iso:type=\"number\">1542.2128</Data>\
                <Data iso:type=\"number\">33.5</Data>\
                <Data iso:type=\"number\">70.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE76</Ind>\
                <Data iso:type=\"number\">1769.0088</Data>\
                <Data iso:type=\"number\">38.0</Data>\
                <Data iso:type=\"number\">76.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE60</Ind>\
                <Data iso:type=\"number\">3050.4062</Data>\
                <Data iso:type=\"number\">39.25</Data>\
                <Data iso:type=\"number\">98.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE10</Ind>\
                <Data iso:type=\"number\">5352.3856</Data>\
                <Data iso:type=\"number\">45.92</Data>\
                <Data iso:type=\"number\">111.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE9L</Ind>\
                <Data iso:type=\"number\">4581.2792</Data>\
                <Data iso:type=\"number\">50.25</Data>\
                <Data iso:type=\"number\">100.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE9T</Ind>\
                <Data iso:type=\"number\">4966.8324</Data>\
                <Data iso:type=\"number\">45.9</Data>\
                <Data iso:type=\"number\">108.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>PRM1</Ind>\
                <Data iso:type=\"number\">5669.9</Data>\
                <Data iso:type=\"number\">44.5</Data>\
                <Data iso:type=\"number\">108.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE77</Ind>\
                <Data iso:type=\"number\">759.7666</Data>\
                <Data iso:type=\"number\">30.0</Data>\
                <Data iso:type=\"number\">63.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE23</Ind>\
                <Data iso:type=\"number\">1111.3004</Data>\
                <Data iso:type=\"number\">32.75</Data>\
                <Data iso:type=\"number\">68.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE20</Ind>\
                <Data iso:type=\"number\">5669.9</Data>\
                <Data iso:type=\"number\">54.5</Data>\
                <Data iso:type=\"number\">103.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B720</Ind>\
                <Data iso:type=\"number\">104008.6456</Data>\
                <Data iso:type=\"number\">130.83</Data>\
                <Data iso:type=\"number\">133.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B742</Ind>\
                <Data iso:type=\"number\">377842.136</Data>\
                <Data iso:type=\"number\">195.67</Data>\
                <Data iso:type=\"number\">152.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B74S</Ind>\
                <Data iso:type=\"number\">317514.4</Data>\
                <Data iso:type=\"number\">195.67</Data>\
                <Data iso:type=\"number\">140.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B74R</Ind>\
                <Data iso:type=\"number\">272155.2</Data>\
                <Data iso:type=\"number\">195.7</Data>\
                <Data iso:type=\"number\">141.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B752</Ind>\
                <Data iso:type=\"number\">115665.96</Data>\
                <Data iso:type=\"number\">124.67</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B752</Ind>\
                <Data iso:type=\"number\">99790.24</Data>\
                <Data iso:type=\"number\">124.83</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B772</Ind>\
                <Data iso:type=\"number\">347451.472</Data>\
                <Data iso:type=\"number\">212.07</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B773</Ind>\
                <Data iso:type=\"number\">340194.0</Data>\
                <Data iso:type=\"number\">212.07</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B701</Ind>\
                <Data iso:type=\"number\">116727.36528</Data>\
                <Data iso:type=\"number\">130.83</Data>\
                <Data iso:type=\"number\">139.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B703</Ind>\
                <Data iso:type=\"number\">141520.704</Data>\
                <Data iso:type=\"number\">142.42</Data>\
                <Data iso:type=\"number\">139.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B703</Ind>\
                <Data iso:type=\"number\">151318.2912</Data>\
                <Data iso:type=\"number\">145.75</Data>\
                <Data iso:type=\"number\">136.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B712</Ind>\
                <Data iso:type=\"number\">54884.632</Data>\
                <Data iso:type=\"number\">93.3333333333</Data>\
                <Data iso:type=\"number\">125.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B720</Ind>\
                <Data iso:type=\"number\">106276.6056</Data>\
                <Data iso:type=\"number\">130.83</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B721</Ind>\
                <Data iso:type=\"number\">76657.048</Data>\
                <Data iso:type=\"number\">108.0</Data>\
                <Data iso:type=\"number\">125.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B722</Ind>\
                <Data iso:type=\"number\">95027.524</Data>\
                <Data iso:type=\"number\">108.0</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B731</Ind>\
                <Data iso:type=\"number\">49895.12</Data>\
                <Data iso:type=\"number\">94.0</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B732</Ind>\
                <Data iso:type=\"number\">52389.876</Data>\
                <Data iso:type=\"number\">93.0</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B733</Ind>\
                <Data iso:type=\"number\">63276.084</Data>\
                <Data iso:type=\"number\">94.75</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B734</Ind>\
                <Data iso:type=\"number\">68038.8</Data>\
                <Data iso:type=\"number\">94.75</Data>\
                <Data iso:type=\"number\">139.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B735</Ind>\
                <Data iso:type=\"number\">61688.512</Data>\
                <Data iso:type=\"number\">94.75</Data>\
                <Data iso:type=\"number\">140.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B736</Ind>\
                <Data iso:type=\"number\">65997.636</Data>\
                <Data iso:type=\"number\">112.58</Data>\
                <Data iso:type=\"number\">125.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B737</Ind>\
                <Data iso:type=\"number\">70079.964</Data>\
                <Data iso:type=\"number\">112.58</Data>\
                <Data iso:type=\"number\">130.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B738</Ind>\
                <Data iso:type=\"number\">79015.7264</Data>\
                <Data iso:type=\"number\">112.58</Data>\
                <Data iso:type=\"number\">141.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B739</Ind>\
                <Data iso:type=\"number\">74389.088</Data>\
                <Data iso:type=\"number\">112.07</Data>\
                <Data iso:type=\"number\">144.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B744</Ind>\
                <Data iso:type=\"number\">394625.04</Data>\
                <Data iso:type=\"number\">213.0</Data>\
                <Data iso:type=\"number\">154.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B753</Ind>\
                <Data iso:type=\"number\">123603.82</Data>\
                <Data iso:type=\"number\">124.83</Data>\
                <Data iso:type=\"number\">142.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B762</Ind>\
                <Data iso:type=\"number\">142881.48</Data>\
                <Data iso:type=\"number\">156.08</Data>\
                <Data iso:type=\"number\">130.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B753</Ind>\
                <Data iso:type=\"number\">158757.2</Data>\
                <Data iso:type=\"number\">156.08</Data>\
                <Data iso:type=\"number\">130.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B772</Ind>\
                <Data iso:type=\"number\">286896.94</Data>\
                <Data iso:type=\"number\">199.9</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B773</Ind>\
                <Data iso:type=\"number\">299370.72</Data>\
                <Data iso:type=\"number\">199.9</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B52</Ind>\
                <Data iso:type=\"number\">221352.896</Data>\
                <Data iso:type=\"number\">185.0</Data>\
                <Data iso:type=\"number\">141.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C97</Ind>\
                <Data iso:type=\"number\">66133.7136</Data>\
                <Data iso:type=\"number\">141.3</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>NOMA</Ind>\
                <Data iso:type=\"number\">4059.6484</Data>\
                <Data iso:type=\"number\">54.0</Data>\
                <Data iso:type=\"number\">69.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>GLEX</Ind>\
                <Data iso:type=\"number\">43091.24</Data>\
                <Data iso:type=\"number\">94.0</Data>\
                <Data iso:type=\"number\">126.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CL60</Ind>\
                <Data iso:type=\"number\">21590.9792</Data>\
                <Data iso:type=\"number\">61.8</Data>\
                <Data iso:type=\"number\">125.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>TRIS</Ind>\
                <Data iso:type=\"number\">4535.92</Data>\
                <Data iso:type=\"number\">53.0</Data>\
                <Data iso:type=\"number\">65.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CL60</Ind>\
                <Data iso:type=\"number\">18710.67</Data>\
                <Data iso:type=\"number\">61.8</Data>\
                <Data iso:type=\"number\">125.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CL44</Ind>\
                <Data iso:type=\"number\">95254.32</Data>\
                <Data iso:type=\"number\">142.3</Data>\
                <Data iso:type=\"number\">123.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C207</Ind>\
                <Data iso:type=\"number\">16510.7488</Data>\
                <Data iso:type=\"number\">91.2</Data>\
                <Data iso:type=\"number\">102.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C150</Ind>\
                <Data iso:type=\"number\">725.7472</Data>\
                <Data iso:type=\"number\">33.5</Data>\
                <Data iso:type=\"number\">55.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C177</Ind>\
                <Data iso:type=\"number\">1133.98</Data>\
                <Data iso:type=\"number\">35.5</Data>\
                <Data iso:type=\"number\">64.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C182</Ind>\
                <Data iso:type=\"number\">1406.1352</Data>\
                <Data iso:type=\"number\">36.0</Data>\
                <Data iso:type=\"number\">92.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C206</Ind>\
                <Data iso:type=\"number\">1632.9312</Data>\
                <Data iso:type=\"number\">36.0</Data>\
                <Data iso:type=\"number\">92.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C402</Ind>\
                <Data iso:type=\"number\">2857.6296</Data>\
                <Data iso:type=\"number\">44.17</Data>\
                <Data iso:type=\"number\">95.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C402</Ind>\
                <Data iso:type=\"number\">2857.6296</Data>\
                <Data iso:type=\"number\">44.17</Data>\
                <Data iso:type=\"number\">95.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C404</Ind>\
                <Data iso:type=\"number\">3810.1728</Data>\
                <Data iso:type=\"number\">46.3</Data>\
                <Data iso:type=\"number\">92.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C414</Ind>\
                <Data iso:type=\"number\">3077.62172</Data>\
                <Data iso:type=\"number\">44.1</Data>\
                <Data iso:type=\"number\">94.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C421</Ind>\
                <Data iso:type=\"number\">3379.2604</Data>\
                <Data iso:type=\"number\">41.7</Data>\
                <Data iso:type=\"number\">96.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C421</Ind>\
                <Data iso:type=\"number\">3102.56928</Data>\
                <Data iso:type=\"number\">41.7</Data>\
                <Data iso:type=\"number\">96.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C441</Ind>\
                <Data iso:type=\"number\">4501.9006</Data>\
                <Data iso:type=\"number\">49.3</Data>\
                <Data iso:type=\"number\">100.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C208</Ind>\
                <Data iso:type=\"number\">3628.736</Data>\
                <Data iso:type=\"number\">52.1</Data>\
                <Data iso:type=\"number\">104.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A37_</Ind>\
                <Data iso:type=\"number\">6350.288</Data>\
                <Data iso:type=\"number\">35.92</Data>\
                <Data iso:type=\"number\">131.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C550</Ind>\
                <Data iso:type=\"number\">6713.1616</Data>\
                <Data iso:type=\"number\">52.17</Data>\
                <Data iso:type=\"number\">112.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C525</Ind>\
                <Data iso:type=\"number\">4808.0752</Data>\
                <Data iso:type=\"number\">46.8</Data>\
                <Data iso:type=\"number\">107.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C25A</Ind>\
                <Data iso:type=\"number\">5669.9</Data>\
                <Data iso:type=\"number\">49.83</Data>\
                <Data iso:type=\"number\">118.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C560</Ind>\
                <Data iso:type=\"number\">7543.23496</Data>\
                <Data iso:type=\"number\">54.08</Data>\
                <Data iso:type=\"number\">108.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C500</Ind>\
                <Data iso:type=\"number\">5375.0652</Data>\
                <Data iso:type=\"number\">47.1</Data>\
                <Data iso:type=\"number\">108.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C550</Ind>\
                <Data iso:type=\"number\">6032.7736</Data>\
                <Data iso:type=\"number\">51.7</Data>\
                <Data iso:type=\"number\">108.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C650</Ind>\
                <Data iso:type=\"number\">9979.024</Data>\
                <Data iso:type=\"number\">53.5</Data>\
                <Data iso:type=\"number\">114.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C560</Ind>\
                <Data iso:type=\"number\">7633.95336</Data>\
                <Data iso:type=\"number\">55.8</Data>\
                <Data iso:type=\"number\">107.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CVLP</Ind>\
                <Data iso:type=\"number\">18955.60968</Data>\
                <Data iso:type=\"number\">91.8</Data>\
                <Data iso:type=\"number\">107.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CVLP</Ind>\
                <Data iso:type=\"number\">22543.5224</Data>\
                <Data iso:type=\"number\">105.33</Data>\
                <Data iso:type=\"number\">104.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CVLP</Ind>\
                <Data iso:type=\"number\">22543.5224</Data>\
                <Data iso:type=\"number\">105.33</Data>\
                <Data iso:type=\"number\">106.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>CVLT</Ind>\
                <Data iso:type=\"number\">24766.1232</Data>\
                <Data iso:type=\"number\">105.3</Data>\
                <Data iso:type=\"number\">107.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>FA20</Ind>\
                <Data iso:type=\"number\">18497.48176</Data>\
                <Data iso:type=\"number\">61.92</Data>\
                <Data iso:type=\"number\">113.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>F900</Ind>\
                <Data iso:type=\"number\">20638.436</Data>\
                <Data iso:type=\"number\">63.42</Data>\
                <Data iso:type=\"number\">100.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>F2TH</Ind>\
                <Data iso:type=\"number\">16238.5936</Data>\
                <Data iso:type=\"number\">63.33</Data>\
                <Data iso:type=\"number\">114.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>ATLA</Ind>\
                <Data iso:type=\"number\">43500.379984</Data>\
                <Data iso:type=\"number\">119.08</Data>\
                <Data iso:type=\"number\">130.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>FA10</Ind>\
                <Data iso:type=\"number\">8300.7336</Data>\
                <Data iso:type=\"number\">42.92</Data>\
                <Data iso:type=\"number\">104.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>FA20</Ind>\
                <Data iso:type=\"number\">12999.94672</Data>\
                <Data iso:type=\"number\">53.5</Data>\
                <Data iso:type=\"number\">107.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DOVE</Ind>\
                <Data iso:type=\"number\">4059.6484</Data>\
                <Data iso:type=\"number\">57.0</Data>\
                <Data iso:type=\"number\">84.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>HERN</Ind>\
                <Data iso:type=\"number\">6123.492</Data>\
                <Data iso:type=\"number\">71.5</Data>\
                <Data iso:type=\"number\">85.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DH2T</Ind>\
                <Data iso:type=\"number\">2313.3192</Data>\
                <Data iso:type=\"number\">48.0</Data>\
                <Data iso:type=\"number\">50.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DHC4</Ind>\
                <Data iso:type=\"number\">12927.372</Data>\
                <Data iso:type=\"number\">95.67</Data>\
                <Data iso:type=\"number\">77.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DHC6</Ind>\
                <Data iso:type=\"number\">5669.9</Data>\
                <Data iso:type=\"number\">65.0</Data>\
                <Data iso:type=\"number\">75.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DHC7</Ind>\
                <Data iso:type=\"number\">19958.048</Data>\
                <Data iso:type=\"number\">93.0</Data>\
                <Data iso:type=\"number\">83.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DH8C</Ind>\
                <Data iso:type=\"number\">18642.6312</Data>\
                <Data iso:type=\"number\">90.0</Data>\
                <Data iso:type=\"number\">90.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>E110</Ind>\
                <Data iso:type=\"number\">5899.871144</Data>\
                <Data iso:type=\"number\">50.3</Data>\
                <Data iso:type=\"number\">92.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>E121</Ind>\
                <Data iso:type=\"number\">5669.9</Data>\
                <Data iso:type=\"number\">47.4</Data>\
                <Data iso:type=\"number\">92.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>PA31</Ind>\
                <Data iso:type=\"number\">3175.144</Data>\
                <Data iso:type=\"number\">40.5833333333</Data>\
                <Data iso:type=\"number\">74.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>D28D</Ind>\
                <Data iso:type=\"number\">4016.55716</Data>\
                <Data iso:type=\"number\">51.0</Data>\
                <Data iso:type=\"number\">74.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A10_</Ind>\
                <Data iso:type=\"number\">23133.192</Data>\
                <Data iso:type=\"number\">57.5</Data>\
                <Data iso:type=\"number\">140.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>VF14</Ind>\
                <Data iso:type=\"number\">19958.048</Data>\
                <Data iso:type=\"number\">70.5</Data>\
                <Data iso:type=\"number\">111.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>LJ25</Ind>\
                <Data iso:type=\"number\">6803.88</Data>\
                <Data iso:type=\"number\">35.6</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>LJ24</Ind>\
                <Data iso:type=\"number\">5896.696</Data>\
                <Data iso:type=\"number\">35.6</Data>\
                <Data iso:type=\"number\">128.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>LJ25</Ind>\
                <Data iso:type=\"number\">6803.88</Data>\
                <Data iso:type=\"number\">35.6</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>LJ28</Ind>\
                <Data iso:type=\"number\">6803.88</Data>\
                <Data iso:type=\"number\">43.7</Data>\
                <Data iso:type=\"number\">120.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>LJ28</Ind>\
                <Data iso:type=\"number\">8300.7336</Data>\
                <Data iso:type=\"number\">39.5</Data>\
                <Data iso:type=\"number\">143.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>GLF2</Ind>\
                <Data iso:type=\"number\">29619.5576</Data>\
                <Data iso:type=\"number\">68.1</Data>\
                <Data iso:type=\"number\">141.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>GLF3</Ind>\
                <Data iso:type=\"number\">31161.7704</Data>\
                <Data iso:type=\"number\">77.1</Data>\
                <Data iso:type=\"number\">136.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>GLF4</Ind>\
                <Data iso:type=\"number\">33837.9632</Data>\
                <Data iso:type=\"number\">77.1</Data>\
                <Data iso:type=\"number\">149.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>GLF4</Ind>\
                <Data iso:type=\"number\">33202.9344</Data>\
                <Data iso:type=\"number\">77.1</Data>\
                <Data iso:type=\"number\">128.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>GLF5</Ind>\
                <Data iso:type=\"number\">41276.872</Data>\
                <Data iso:type=\"number\">93.5</Data>\
                <Data iso:type=\"number\">145.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A748</Ind>\
                <Data iso:type=\"number\">21092.028</Data>\
                <Data iso:type=\"number\">102.46</Data>\
                <Data iso:type=\"number\">94.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>TRID</Ind>\
                <Data iso:type=\"number\">71667.536</Data>\
                <Data iso:type=\"number\">98.0</Data>\
                <Data iso:type=\"number\">146.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A748</Ind>\
                <Data iso:type=\"number\">22679.6</Data>\
                <Data iso:type=\"number\">98.2</Data>\
                <Data iso:type=\"number\">100.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>WW23</Ind>\
                <Data iso:type=\"number\">10659.412</Data>\
                <Data iso:type=\"number\">44.8</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>ASTR</Ind>\
                <Data iso:type=\"number\">11181.0428</Data>\
                <Data iso:type=\"number\">54.7</Data>\
                <Data iso:type=\"number\">126.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>ARVA</Ind>\
                <Data iso:type=\"number\">6803.88</Data>\
                <Data iso:type=\"number\">68.8</Data>\
                <Data iso:type=\"number\">81.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>ARVA</Ind>\
                <Data iso:type=\"number\">6803.88</Data>\
                <Data iso:type=\"number\">68.8</Data>\
                <Data iso:type=\"number\">81.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>JCOM</Ind>\
                <Data iso:type=\"number\">7620.3456</Data>\
                <Data iso:type=\"number\">43.3</Data>\
                <Data iso:type=\"number\">130.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>WW24</Ind>\
                <Data iso:type=\"number\">10659.412</Data>\
                <Data iso:type=\"number\">44.8</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>WW24</Ind>\
                <Data iso:type=\"number\">10659.412</Data>\
                <Data iso:type=\"number\">44.8</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>IL18</Ind>\
                <Data iso:type=\"number\">61071.62688</Data>\
                <Data iso:type=\"number\">122.7</Data>\
                <Data iso:type=\"number\">103.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>IL76</Ind>\
                <Data iso:type=\"number\">169999.47772</Data>\
                <Data iso:type=\"number\">165.7</Data>\
                <Data iso:type=\"number\">119.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C130</Ind>\
                <Data iso:type=\"number\">70306.76</Data>\
                <Data iso:type=\"number\">132.07</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C130</Ind>\
                <Data iso:type=\"number\">70306.76</Data>\
                <Data iso:type=\"number\">132.6</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C130</Ind>\
                <Data iso:type=\"number\">70306.76</Data>\
                <Data iso:type=\"number\">132.07</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C130</Ind>\
                <Data iso:type=\"number\">70306.76</Data>\
                <Data iso:type=\"number\">132.6</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>L101</Ind>\
                <Data iso:type=\"number\">195044.56</Data>\
                <Data iso:type=\"number\">155.3</Data>\
                <Data iso:type=\"number\">138.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>L101</Ind>\
                <Data iso:type=\"number\">211373.872</Data>\
                <Data iso:type=\"number\">155.3</Data>\
                <Data iso:type=\"number\">140.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>L101</Ind>\
                <Data iso:type=\"number\">211373.872</Data>\
                <Data iso:type=\"number\">155.3</Data>\
                <Data iso:type=\"number\">144.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>L101</Ind>\
                <Data iso:type=\"number\">231331.92</Data>\
                <Data iso:type=\"number\">155.3</Data>\
                <Data iso:type=\"number\">144.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>L101</Ind>\
                <Data iso:type=\"number\">234053.472</Data>\
                <Data iso:type=\"number\">155.3</Data>\
                <Data iso:type=\"number\">148.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>L29A</Ind>\
                <Data iso:type=\"number\">19844.65</Data>\
                <Data iso:type=\"number\">54.4</Data>\
                <Data iso:type=\"number\">132.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C141</Ind>\
                <Data iso:type=\"number\">143607.2272</Data>\
                <Data iso:type=\"number\">159.9</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C141</Ind>\
                <Data iso:type=\"number\">155582.056</Data>\
                <Data iso:type=\"number\">159.9</Data>\
                <Data iso:type=\"number\">129.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C5</Ind>\
                <Data iso:type=\"number\">348812.248</Data>\
                <Data iso:type=\"number\">222.7</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>C5</Ind>\
                <Data iso:type=\"number\">379656.504</Data>\
                <Data iso:type=\"number\">222.7</Data>\
                <Data iso:type=\"number\">135.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>P3</Ind>\
                <Data iso:type=\"number\">61234.92</Data>\
                <Data iso:type=\"number\">99.7</Data>\
                <Data iso:type=\"number\">134.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>A4_</Ind>\
                <Data iso:type=\"number\">11113.004</Data>\
                <Data iso:type=\"number\">27.5</Data>\
                <Data iso:type=\"number\">120.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DC10</Ind>\
                <Data iso:type=\"number\">200941.256</Data>\
                <Data iso:type=\"number\">155.3</Data>\
                <Data iso:type=\"number\">136.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DC7</Ind>\
                <Data iso:type=\"number\">64863.656</Data>\
                <Data iso:type=\"number\">127.5</Data>\
                <Data iso:type=\"number\">110.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>DC85</Ind>\
                <Data iso:type=\"number\">147417.4</Data>\
                <Data iso:type=\"number\">142.4</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>MD11</Ind>\
                <Data iso:type=\"number\">273289.18</Data>\
                <Data iso:type=\"number\">169.8</Data>\
                <Data iso:type=\"number\">155.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE40</Ind>\
                <Data iso:type=\"number\">7135.00216</Data>\
                <Data iso:type=\"number\">43.5</Data>\
                <Data iso:type=\"number\">100.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>MU2</Ind>\
                <Data iso:type=\"number\">5250.3274</Data>\
                <Data iso:type=\"number\">39.1666666667</Data>\
                <Data iso:type=\"number\">88.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>MU2</Ind>\
                <Data iso:type=\"number\">4898.7936</Data>\
                <Data iso:type=\"number\">39.2</Data>\
                <Data iso:type=\"number\">119.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B2</Ind>\
                <Data iso:type=\"number\">152633.708</Data>\
                <Data iso:type=\"number\">172.0</Data>\
                <Data iso:type=\"number\">140.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AEST</Ind>\
                <Data iso:type=\"number\">2864.43348</Data>\
                <Data iso:type=\"number\">36.67</Data>\
                <Data iso:type=\"number\">94.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>PA31</Ind>\
                <Data iso:type=\"number\">2812.2704</Data>\
                <Data iso:type=\"number\">40.7</Data>\
                <Data iso:type=\"number\">100.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>PAY4</Ind>\
                <Data iso:type=\"number\">5465.7836</Data>\
                <Data iso:type=\"number\">47.7</Data>\
                <Data iso:type=\"number\">110.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AN2</Ind>\
                <Data iso:type=\"number\">5499.803</Data>\
                <Data iso:type=\"number\">59.67</Data>\
                <Data iso:type=\"number\">54.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>BE40</Ind>\
                <Data iso:type=\"number\">7302.8312</Data>\
                <Data iso:type=\"number\">43.06</Data>\
                <Data iso:type=\"number\">111.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC11</Ind>\
                <Data iso:type=\"number\">5216.308</Data>\
                <Data iso:type=\"number\">46.0</Data>\
                <Data iso:type=\"number\">75.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC95</Ind>\
                <Data iso:type=\"number\">4683.3374</Data>\
                <Data iso:type=\"number\">52.2</Data>\
                <Data iso:type=\"number\">121.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC50</Ind>\
                <Data iso:type=\"number\">3061.746</Data>\
                <Data iso:type=\"number\">49.08</Data>\
                <Data iso:type=\"number\">97.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC56</Ind>\
                <Data iso:type=\"number\">2948.348</Data>\
                <Data iso:type=\"number\">49.0833333333</Data>\
                <Data iso:type=\"number\">97.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC68</Ind>\
                <Data iso:type=\"number\">3401.94</Data>\
                <Data iso:type=\"number\">49.0833333333</Data>\
                <Data iso:type=\"number\">97.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>B1_</Ind>\
                <Data iso:type=\"number\">216363.384</Data>\
                <Data iso:type=\"number\">137.0</Data>\
                <Data iso:type=\"number\">165.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC52</Ind>\
                <Data iso:type=\"number\">2494.756</Data>\
                <Data iso:type=\"number\">44.1</Data>\
                <Data iso:type=\"number\">97.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC80</Ind>\
                <Data iso:type=\"number\">4059.6484</Data>\
                <Data iso:type=\"number\">49.05</Data>\
                <Data iso:type=\"number\">97.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>AC90</Ind>\
                <Data iso:type=\"number\">4649.318</Data>\
                <Data iso:type=\"number\">46.67</Data>\
                <Data iso:type=\"number\">97.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SBR1</Ind>\
                <Data iso:type=\"number\">8459.4908</Data>\
                <Data iso:type=\"number\">44.5</Data>\
                <Data iso:type=\"number\">120.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SBR1</Ind>\
                <Data iso:type=\"number\">9071.84</Data>\
                <Data iso:type=\"number\">44.5</Data>\
                <Data iso:type=\"number\">120.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SBR1</Ind>\
                <Data iso:type=\"number\">10886.208</Data>\
                <Data iso:type=\"number\">50.5</Data>\
                <Data iso:type=\"number\">105.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SBR2</Ind>\
                <Data iso:type=\"number\">10568.6936</Data>\
                <Data iso:type=\"number\">44.5</Data>\
                <Data iso:type=\"number\">137.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SBR2</Ind>\
                <Data iso:type=\"number\">11113.004</Data>\
                <Data iso:type=\"number\">50.4</Data>\
                <Data iso:type=\"number\">128.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SH33</Ind>\
                <Data iso:type=\"number\">9979.024</Data>\
                <Data iso:type=\"number\">74.67</Data>\
                <Data iso:type=\"number\">96.0</Data>\
        </Atom>\
        <Atom>\
                <Rel>aircraftChar</Rel>\
                <Ind>SH36</Ind>\
                <Data iso:type=\"number\">11793.392</Data>\
                <Data iso:type=\"number\">74.8</Data>\
                <Data iso:type=\"number\">104.0</Data>\
        </Atom>\
     </Assert>").

test(50,
     [(p('$V'(x),'$V'(y)):-true,true)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>p</Rel>\
                                <Var>x</Var>\
                                <Var>y</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <And></And>\
                </if>\
        </Implies>\
     </Assert>").

test(51,
     [(p('$V'(x),'$V'(y)) :- true, q)],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>p</Rel>\
                                <Var>x</Var>\
                                <Var>y</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <And>\
                                <Atom>\
                                        <Rel>q</Rel>\
                                </Atom>\
                        </And>\
                </if>\
        </Implies>\
     </Assert>").

test(52,
     [(p('$V'(x),'$V'(y)):-(false ; false))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>p</Rel>\
                                <Var>x</Var>\
                                <Var>y</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <Or></Or>\
                </if>\
        </Implies>\
     </Assert>").

test(53,
     [(p('$V'(x),'$V'(y)) :- (false ; q))],
     [],
     "<Assert mapClosure=\"universal\">\
        <Implies>\
                <then>\
                        <Atom>\
                                <Rel>p</Rel>\
                                <Var>x</Var>\
                                <Var>y</Var>\
                        </Atom>\
                </then>\
                <if>\
                        <Or>\
                                <Atom>\
                                        <Rel>q</Rel>\
                                </Atom>\
                        </Or>\
                </if>\
        </Implies>\
     </Assert>").


test_bimetatrans :-
    catch((test_1,
           test_2,
           test_3,
           test_4,
           test_5,
           test_6,
           test_7,
           test_8,
           test_9,
           test_10,
           test_11,
           test_12,
           test_13,
           test_14,
           test_15,
           test_16,
           test_17,
           test_18,
           test_19,
           test_20,
           test_21,
           test_22,
           test_23,
           test_24,
           test_25,
           test_26,
           test_27,
           test_28,
           test_29,
           test_30,
           test_31,
           test_32,
           test_33,
           test_34,
           test_35,
           test_36,
           test_37,
           test_38,
           test_39,
           test_40,
           test_41,
           test_42,
           test_43,
           test_44,
           test_45,
           test_46,
           test_47,
           test_48,
           test_49,
           test_50,
           test_51,
	       test_52,
	       test_53),
          E,
          (writeq(E),
           nl,
           false)).

:- initialization(test_bimetatrans).
