:- module(bimetatrans, [parse_ruleml/3]).

:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).

:- set_prolog_flag(double_quotes, chars).

/*
 * In all comments:
 *
 * Prolog/'$V' stands for "Metalogic Prolog with variable-as-'$V'-term encoding"
 * RuleML/XML stands for "RuleML in XML with any kind of rendering"
 * RuleML/xmL stands for "RuleML in minified XML"
 * RuleML/Xml stands for "RuleML in indented XML"
 *
 * "Minified XML" refers to XML with only necessary whitespace,
 * between element names and attributes, and pairs of attributes, with
 * all indentation stripped out. "Indented XML" contains indentation
 * and newlines, and is usually formatted for human readers.
 *
 * parse_ruleml/3 is the sole public predicate of BiMetaTrans(Prolog,
 * RuleML), a bidirectional translator capable of parsing well-formed
 * RuleML/XML (valid w.r.t. a proposed anchor schema nafhornlogeq
 * defining a sublanguage of the existing anchor schema naffologeq) to
 * an equivalent Prolog/'$V' term and back to RuleML/xmL. It has the
 * modes
 *
 * +AssertItems, +QueryItems, ?XML    (Prolog->RuleML)
 * ?AssertItems, ?QueryItems, +XML    (RuleML->Prolog)
 *
 * The modes constrain the inputs to fit one of two patterns, the
 * first where AssertItems and QueryItems are instantiated and XML is
 * possibly a variable, and conversely for the second. Instantiated
 * inputs are expected to be ground, meaning they should not contain
 * free variables.
 *
 * A RuleML/XML document is assumed to contain an optional Assert
 * element (with zero or more children) and zero or more Query
 * elements. The children of the Assert element are the Items of
 * AssertItems, while the Items of QueryItems each correspond to a
 * single Query element.
 *
 * parse_ruleml/3 is meant to subsume an invertible function in the
 * sense that the top-level query
 *
 * ?- parse_ruleml(AssertItems, QueryItems, XML0),    % Prolog->RuleML
 *    parse_ruleml(AssertItems0, QueryItems0, XML),   % RuleML->Prolog
 *    AssertItems0 == AssertItems,                    % Test for expected round-trip results.
 *    QueryItems0 == QueryItems,
 *    XML0 == XML.
 *
 * should always evaluate to true when the variables whose names are
 * not 0-appended are instantiated and therefore ground.
 */

parse_ruleml(AssertItems, QueryItems, XML) :-
    (  ( var(AssertItems) ; var(QueryItems) ), var(XML) ->
       throw(error(instantiation_error, parse_ruleml/2))
    ;  phrase(ruleml_top_level_items(AssertItems, QueryItems), XML),
       !
    ).


/*
 * parse_header//0 matches an existing RuleML/XML header exactly to
 * the text of the strings (in case we are parsing text).
 *
 * Since parse_header consumes no arguments, it does not produce
 * corresponding Prolog/'$V' terms. Generally, the generation of
 * Prolog/'$V' terms is signified by the presence of arguments in
 * productions.
 */

parse_header -->
    list_ws("<?xml version=\"1.0\" encoding=\"UTF-8\"?>"),
    list_ws("<?xml-model href=\"http://deliberation.ruleml.org\
/1.02/xsd/naffologeq.xsd\"?>").


/*
 * ruleml_top_level_items//2 drives the main loop of the grammar in
 * either direction, and sets the mould for a recurrent pattern when
 * processing RuleML/XML elements represented in Prolog/'$V' as
 * lists. After parse_header succeeds, the grammar proceeds to
 * top-level elements in the RuleML/XML Knowledge Base (KB), each item
 * of which may be either a Assert or a Query, of which Assert must
 * appear first.  There may be up to one Assert.
 *
 * The two arguments are (un)instantiated depending on the direction
 * in which parse_ruleml/2 operates. In either direction, once
 * ruleml_query_item(QueryItems) or ruleml_assert(AssertItems)
 * succeeds, AssertItems and QueryItems are ground lists of terms,
 * corresponding to Assert/Query performative(s) of the RuleML/XML KB.
 */

ruleml_top_level_items(AssertItems, QueryItems) -->
    (  ruleml_assert(AssertItems),
       ruleml_query_items(QueryItems)
    ;  { AssertItems = [] },
       ruleml_query_items(QueryItems)
    ).

/*
 * ruleml_assert//1 is the first production to make the
 * division between the two directions of translation explicit. A
 * translation direction is decided by the instantiation of the
 * argument variable Items. This pattern will recur
 * many times in subsequent productions, so to avoid repeating
 * ourselves later, we now describe the implementation more deeply.
 *
 * If Items is a free variable (as determined by the var primitive)
 * then, after the success of the translation, it is bound to a list
 * of terms representing the items of the RuleML/XML <Assert>...</Assert>
 * element in the order in which they appear in the ground XML.
 *
 * Conversely, Items is supposed to be bound to a list of Prolog/'$V'
 * terms representing the items of an <Assert>...</Assert> element.
 * Processing the Prolog/'$V' terms results in the corresponding
 * RuleML/xmL being inserted between the Assert tags.
 *
 * To understand how this works in either translation direction, we
 * now describe the implementation more deeply. The RuleML/XML is not
 * represented as an explicit argument of ruleml_assert//1, but is
 * present nonetheless. Scryer Prolog implements DCGs using rules it
 * gives to its term expansion facility. The term expansion rules tell
 * Scryer how DCG productions are to be structurally expanded into
 * Prolog clauses it can directly compile. It is during the term
 * expansion phase of compilation that clause head arguments for
 * RuleML/XML are created; this is why explicit arguments for the
 * RuleML string are not needed in the heads of the productions
 * themselves. The declaration
 *
 * :- set_prolog_flag(double_quotes, chars).
 *
 * at the beginning of this source file states that strings (that is,
 * characters enclosed in double quotes) are to be treated by the
 * Prolog engine as lists of characters. Since lists in Prolog have a
 * head and tail available as structural components at all times, and
 * since Prolog does not require programmers to instantiate variables
 * immediately, a common technique of list manipulation is to leave
 * list tails uninstantiated until some later time. That way, lists
 * can be appended to incrementally and in constant time, as long as a
 * declarative 'pointer' (a logic variable bound) to the tail variable
 * is kept. A partially instantiated list of this form is commonly
 * known as a "difference list."
 *
 * DCGs maintain an underlying difference list of grammar items
 * through two additional arguments in their heads: one to the head of
 * the difference list, and one to the as-yet uninstantiated tail. It
 * is worth pointing out again that these variables are added during
 * term expansion. As an example, ruleml_assert//1 will be expanded to
 * something like
 *
 * ruleml_assert(Items) -->  ...
 *
 * ~~>
 *
 * ruleml_assert(Items, XML, XML0) :-  ...
 *
 * where XML = [<UTF-8 characters> ... | XML0].
 *
 * In either direction, the production ruleml_assert_items//1
 * qualifies Assert items. An empty <Assert></Assert> element in
 * RuleML/XML translates to an empty list bound to Items. In
 * the reverse direction, an empty list bound to Items at the
 * outset of ruleml_assert//1 will cause it to fail, meaning that
 * an empty <Assert></Assert> element is never emitted to the output
 * RuleML/xmL.
 */

ruleml_assert(Items) -->
    (  { var(Items) } ->
       list_ws("<Assert mapClosure=\"universal\">"),
       ruleml_assert_items(Items),
       list_ws("</Assert>")
    ;  "<Assert mapClosure=\"universal\">",
       { Items \== [] },
       ruleml_assert_items(Items),
       "</Assert>"
    ).


/*
 * ruleml_assert_items//1 and ruleml_query_items//1 greedily consume
 * items from the grammar and represent each as an Item. They stock
 * Item's to their sole argument, a list, until there are no items
 * left to be generated. There are no provisions necessary to make
 * the predicates work in either translation direction.
 *
 * The greedy list building pattern recurs in several places in this
 * source file:
 *
 * 1) ruleml_item_conjunction
 * 2) ruleml_item_disjunction
 * 3) ruleml_atoms
 */

ruleml_assert_items([Item | Items]) -->
    ruleml_assert_item(Item),
    ruleml_assert_items(Items).
ruleml_assert_items([]) --> [].


ruleml_query_items(Items) -->
    (  { var(Items) } ->
       ruleml_query_item(Item),
       (  { var(Item) } ->
          ruleml_query_items(Items)
       ;  { Items = [Item | Items0] },
          ruleml_query_items(Items0)
       )
    ;  { Items = [Item | Items0] },
       ruleml_query_item(Item),
       ruleml_query_items(Items0)
    ).
ruleml_query_items([]) --> [].


/*
 * ruleml_query_item//1 is defined according to the pattern
 * established in ruleml_assert//1. Here, Item is expected to take
 * the form (?- Item0), where Item0 is a single Prolog/'$V' term that can
 * be either
 *
 * 1) A term representing a RuleML atom, logical equality, or Naf
 * form, or,
 *
 * 2) A conjunction of the terms described in 1), whose conjuncts are
 * distributed over the Prolog comma functor, i.e., (a, (b, (c, d))).
 * The associativity of the Prolog comma operator allows the term
 * to be equivalently written as (a,b,c,d).
 */

ruleml_query_item(Item) -->
    (  { var(Item) } ->
       list_ws("<Query closure=\"existential\">"),
       (  ruleml_condition(Item0),
          { Item = (?- Item0) } ->
          { true }
       ;  { true }
       ),
       list_ws("</Query>")
    ;  "<Query closure=\"existential\">",
       { Item = (?- Item0) },
       ruleml_condition(Item0),
       "</Query>"
    ).


/*
 * These nonterminals match the lexical elements they name. Those
 * that have no arguments produce no corresponding Prolog
 * items. Whitespace, for example, is discarded immediately after
 * being read.
 *
 * list_ws reads a string into its argument as a partial
 * string before consuming any following whitespace.
 */

ws --> ( "\n" | "\a" | "\t" | "\r" | "\v" | " " ) -> ws.
ws --> [].


underscore('_') --> "_".

space(' ') --> " ".

decimal_point('.') --> ".".

sign('-') --> "-".
sign('+') --> "+".

double_quote('"') --> "\"".

list_ws(Ls) -->
    list(Ls),
    ws.

list([]) --> [].
list([L|Ls]) --> [L], list(Ls).

/*
 * ruleml_assert_item//1 specifies the elements of RuleML that may
 * appear as items in a RuleML Assert performative, an implicitly
 * conjunctive form in that it asserts all of its KB items. It is the core
 * production of ruleml_assert//1, responsible for the generation of
 * RuleML Assert elements.
 *
 * ruleml_assert_item//1 uses the '|' operator to create an ordered
 * disjunction of the operand productions. DCGs use '|' to imitate the
 * 'choice' operator of the EBNF metasyntax:
 *
 * RULE ::= PROD_1 | PROD_2 | ... | PROD_N;;
 *
 * While ruleml_implies and ruleml_equal recognize disjoint sets of
 * Prolog/'$V' terms, whose members are represented by Item, ruleml_atom
 * recognizes both sets and therefore comes last.
 */

ruleml_assert_item(Item) -->
    ruleml_implies(Item) | ruleml_equal(Item) | ruleml_atom(Item).


/*
 * ruleml_condition//1 recognizes the set of condition items. As in
 * ruleml_assert_item//1, we can think of '|' as inducing a union
 * among the sets recognized by the named subgrammars.
 */

ruleml_condition(Item) -->
    ruleml_conjunction_of_items(Item) | ruleml_disjunction_of_items(Item) |
    ruleml_atom(Item) | ruleml_equal(Item) | ruleml_naf(Item).


/*
 * See the comment block for ruleml_assert_items//1 and
 * ruleml_query_items//1 for an explanation of
 * ruleml_item_conjunction//1.
 */

ruleml_item_conjunction([Item | Items]) -->
    ruleml_condition(Item),
    ruleml_item_conjunction(Items).
ruleml_item_conjunction([]) --> [].


/*
 * ruleml_conjunction_of_items//1 uses ruleml_item_conjunction//1 to
 * match lists of conjunction elements enclosed in <And>...</And>
 * tags. The { ItemsList = [_,_|_] } check prevents the acceptance of
 * <And>...</And> elements with fewer than two children. However,
 * RuleML/XML documents may contain <And>...</And> elements with fewer
 * than two subelements, and these cases are handled by similar
 * unifications, which check for only one or no items in ItemsList.
 *
 * In either translation direction, we expect Items to be a
 * comma-functored list of terms representing a conjuction of items.
 * "Comma-functored list" here refers to Prolog/'$V' terms of the form
 *
 * (a, b, c, d, e) = (a, (b, (c, (d, e))))
 *
 * The nicer form of the left hand side is syntactically equivalent to
 * that of the right hand side thanks to the precedence of the comma (,)
 * operator, which is right-associative in Prolog.
 *
 * Since comma (,) is a binary Prolog operator, it must contain at
 * least two terms. comma (,) is used by the translator to distinguish
 * <And>...</And> elements in RuleML/XML from elements that are also
 * represented as functors on the Prolog/'$V' side. If the <And>...</And>
 * element contains fewer than two terms, we substitute for "missing"
 * terms in the (,) functor with the Prolog/'$V' term "true." "true"
 * evaluates to true at the top-level.
 *
 * While generally the two directions of translations are divided into
 * separate branches, there is considerable syntactic and semantic
 * symmetry about the branches in cases like this one, as fold_commas
 * is the inverse of unfold_commas. fold_commas transforms suitably
 * inhabited lists to comma-functored lists, and unfold_commas works
 * symmetrically, i.e., in the opposite direction.
 */

ruleml_conjunction_of_items(Items) -->
    (  { var(Items) } ->
       list_ws("<And>"),
       ruleml_item_conjunction(ItemsList),
       (  { ItemsList = [_,_|_] } ->
          { fold_commas(ItemsList, Items) }
       ;  { ItemsList = [Item0] } ->
          { Items = (true, Item0) }
       ;  { ItemsList = [] } ->
          { Items = (true, true) }
       ),
       list_ws("</And>")
    ;  "<And>",
       (  { Items = (true, true) } ->
          { true }
       ;  { Items = (true, Item0) } ->
          ruleml_item_conjunction([Item0])
       ;  { Items = (_,_) },
          { unfold_commas(Items, ItemsList) },
          ruleml_item_conjunction(ItemsList)
       ),
       "</And>"
    ).

/*
 * See the comment block for ruleml_assert_items//1 and
 * ruleml_query_items//1 for an explanation of
 * ruleml_item_disjunction//1.
 */

ruleml_item_disjunction([Item | Items]) -->
    ruleml_condition(Item),
    ruleml_item_disjunction(Items).
ruleml_item_disjunction([]) --> [].


/*
 * See the documentation of ruleml_conjunction_of_items//1; the only
 * differences between ruleml_disjunction_of_items//1 and it is that
 * the disjunctive form uses (;) in place of (,), and that
 * fold_semicolons and unfold_semicolons take the place of their
 * counterparts fold_commas and unfold_commas. <Or>...</Or> elements
 * substitute for <And>...</And> elements in RuleML/XML, and "false"
 * substitutes for "true".
 */

ruleml_disjunction_of_items(Items) -->
    (  { var(Items) } ->
       list_ws("<Or>"),
       ruleml_item_disjunction(ItemsList),
       (  { ItemsList = [_,_|_] } ->
          { fold_semicolons(ItemsList, Items) }
       ;  { ItemsList = [Item0] } ->
          { Items = (false ; Item0) }
       ;  { ItemsList = [] } ->
          { Items = (false ; false) }
       ),
       list_ws("</Or>")
    ;  "<Or>",
       (  { Items = (false ; false) } ->
          { true }
       ;  { Items = (false ; Item0) } ->
          ruleml_item_disjunction([Item0])
       ;  { Items = (_ ; _) } ->
          { unfold_semicolons(Items, ItemsList) },
          ruleml_item_disjunction(ItemsList)
       ),
       "</Or>"
    ).


split_plex(Xs, PlexItems, RepoItem) :-
    (  var(Xs) ->
       PlexItems = [],
       RepoItem = Xs
    ;  Xs = [R|Rs] ->
       PlexItems = [R|Ps],
       split_plex(Rs, Ps, RepoItem)
    ;  PlexItems = [],
       RepoItem = Xs
    ).

/*
 * Single-tuple Plexes are RuleML's counterpart to Prolog/'$V''s
 * lists. Before describing how they are handled by the translator, we
 * introduce an additional piece of terminology. A "repo" is a "rest
 * positional" item referring to what Prolog would call the tail of a
 * list. Often, in RuleML KBs, a repo is restricted to be either a
 * variable or another plex, although in Prolog, a list tail may be
 * anything at all.
 *
 * ruleml_plex//1 follows the now established pattern of splitting the
 * translation directions across two branches at its root. If Plex is
 * a variable, the items between the <Plex>...</Plex> tags are
 * captured before checking for a tailing <repo>...</repo> element.
 *
 * Notice that only ruleml_var//1 is invoked to consume the repo
 * contents. This is because Prolog flattens its lists implicitly,
 * whenever it can. Therefore, a Plex with another Plex as its repo
 * element is represented on the Prolog/'$V' side as a list (the outer
 * Plex) with another list (the repo Plex) as its tail. The extent of
 * the RuleML Plex must end eventually, terminating in a variable, and
 * so, it is enough for ruleml_plex//1 to consume only RuleML
 * variables in Plex repo's.
 *
 * On the Prolog/'$V' side of translation, the ISO predicate
 * acyclic_term is used to ensure that Plex, as distinguished from the
 * representations of other RuleML atoms by the list functor ('.'), is
 * not cyclic. A Prolog list is cyclic if its tail points to any list
 * cell in the chain of cells connecting its tail and head. Similarly,
 * Plex should not be a string, which is effectively considered a type
 * of list under the module's double_flags setting in Scryer Prolog.
 */

ruleml_plex(Plex) -->
    (  { var(Plex) } ->
       (  list_ws("<Plex>") ->
          ruleml_items(PlexItems),
          (  list_ws("<repo>") ->
             ruleml_var(RepoVar),
             list_ws("</repo>"),
             { append(PlexItems, RepoVar, Plex) }
          ;  { Plex = PlexItems }
          ),
          list_ws("</Plex>")
       ;  list_ws("<Plex/>")
       )
    ;  {  ( \+ partial_string(Plex) ; Plex == [] ),
          acyclic_term(Plex) },
       (  {  functor(Plex, ('.'), 2) } ->
          {  split_plex(Plex, PlexItems, RepoVar) },
          "<Plex>",
          ruleml_items(PlexItems),
          (  { RepoVar \== [] } ->
             "<repo>",
             ruleml_var(RepoVar),
             "</repo>"
          ;  { true }
          ),
          "</Plex>"
       ;  { Plex == [] } ->
          "<Plex/>"
       )
    ).


/*
 * ruleml_naf//1 is a slight variation on previous patterns of
 * explicitly divided translation, with symmetry across the branch
 * boundary and even fewer constraints.  Naf forms can only negate
 * items that appear in RuleML conditions, and are distinguished
 * from other RuleML atoms by the (\+) functor, which is the
 * negation as failure operator in Prolog.
 */

ruleml_naf(Item) -->
    (  { var(Item) } ->
       list_ws("<Naf>"),
       ruleml_condition(NafItem),
       { Item = (\+ NafItem) },
       list_ws("</Naf>")
    ;  "<Naf>",
       { Item = (\+ NafItem) },
       ruleml_condition(NafItem),
       "</Naf>"
    ).


/*
 * ruleml_assert_items//1 and ruleml_query_items//1 are nearly
 * identical to ruleml_atoms//1, substituting their own subgrammars
 * for ruleml_atom(s).
 */

ruleml_atoms([Item|Items]) -->
    ruleml_atom(Item),
    ruleml_atoms(Items).
ruleml_atoms([]) --> [].


/*
 * ruleml_atom//1 follows the split translation pattern.
 * It is the template for the more elaborate instantiations. Its
 * central functor is the (=..)/2 operator of ISO Prolog. (=..)/2 is
 * itself bidirectional.  It destructures functors to their underlying
 * components, their head Prolog atom and the functor's arguments. As
 * an example, the Prolog functor f(a,b,c) destructures to the list
 *
 * [f, a, b, c]
 *
 * on the right hand side. Dually, the query
 *
 * ?- F =.. [f, a, b, c]
 *
 * made at the Prolog top-level posts the goal, F = f(a,b,c).
 *
 * Thus, the use of (=..)/2 in either translation direction is
 * relative to whenever Name (the value of the Prolog/'$V' functor/RuleML
 * atom) and Args (the contents of the Prolog/'$V' functor/RuleML atom) are
 * instantiated. Here, no special checks need to be made aside from
 * checking that the name of the Prolog/'$V' functor/RuleML atom is not (,)
 * or (;). As outlined in previous comments, those functor names are
 * reserved for <And>...</And> and <Or>...</Or> elements.
 */

ruleml_atom(Item) -->
    (  { var(Item) } ->
       list_ws("<Atom>"),
       list_ws("<Rel>"),
       prolog_symbol(Name),
       list_ws("</Rel>"),
       ruleml_items(Args),
       list_ws("</Atom>"),
       { Item =.. [Name | Args] }
    ;  { Item =.. [Name | Args] },
       "<Atom>",
       "<Rel>",
       prolog_symbol(Name),
       "</Rel>",
       ruleml_items(Args),
       "</Atom>"
    ).

/*
 * ruleml_items greedily consumes ruleml_item terms and populates the
 * list Items with them. Conversely, in the opposite direction,
 * ruleml_items emits XML corresponding to each term of Items, a
 * ground Prolog/'$V' list.
 */

ruleml_items(Items) -->
    (  { var(Items) } ->
       (  ruleml_item(Arg) ->
          { Items = [Arg | Args] },
          ruleml_items(Args)
       ;  { Items = [] }
       )
    ;  (  { Items = [Arg | Args] } ->
          (  ruleml_item(Arg) ->
             ruleml_items(Args)
          )
       ;  { Items = [] }
       )
    ).


/*
 * The ruleml_item//1 nonterminal defines a RuleML item as being in
 * the union of the sets of Item belonging to the subgrammars named by
 * the nonterminal disjuncts.
 */
ruleml_item(Item) -->
    ruleml_equal(Item) | ruleml_var(Item) | ruleml_ind(Item) |
    ruleml_plex(Item) | ruleml_data(Item) |  ruleml_expr(Item).


/*
 * RuleML expressions can represent function terms in first-order
 * logic, which are necessarily child terms of parent predicates
 * (including of a distinguished 'Equal' predicate). Expressions can
 * contain rest positional, or repo terms, which are similar to the
 * related construct discussed in the comment block for ruleml_plex//1.
 *
 * Since they appear as functors on the Prolog/'$V' side of
 * translation, just as RuleML atoms do, the (=..)/2 functor is
 * employed here.
 */

ruleml_expr(Item) -->
    (  { var(Item) } ->
       list_ws("<Expr>"),
       list_ws("<Fun>"),
       prolog_symbol(Name),
       list_ws("</Fun>"),
       ruleml_items(Args),
       (  list_ws("<repo>"),
          ruleml_item(RepoItem),
          list_ws("</repo>"),
          { fold_commas(Args, ArgsCommas) },
          { Item =.. [Name, (ArgsCommas | RepoItem)] }
       ;  { Item =.. [Name | Args] }
       ),
       list_ws("</Expr>")
    ;  { Item =.. [Name | Args] },
       "<Expr>",
       "<Fun>",
       prolog_symbol(Name),
       "</Fun>",
       (  { Args = [(InnerArgs | RepoItem)] } ->
          {  InnerArgs = (_,_) -> unfold_commas(InnerArgs, InnerArgsList)
             ;  InnerArgsList = [InnerArgs] },
          ruleml_items(InnerArgsList),
          "<repo>",
          ruleml_item(RepoItem),
          "</repo>"
       ;  ruleml_items(Args)
       ),
       "</Expr>"
    ).


/*
 * An <Ind>...</Ind> element refers to an individual in RuleML/XML, a
 * distinct entity or situation or circumstance in a RuleML knowledge
 * base.  The translator uses the simple heuristic that individuals
 * are otherwise like Prolog atoms (to be sharply distinguished from
 * logical and RuleML atoms), except that their names are
 * capitalized. In ISO Prolog, this requires them to be enclosed in
 * single quotes in order to be typed as Prolog atoms.
 */

ruleml_ind(Name) -->
    (  { var(Name) } ->
       list_ws("<Ind>"),
       ruleml_ind_helper(Cs),
       list_ws("</Ind>"),
       { atom_chars(Name, Cs) }
    ;  { atom(Name) },
       "<Ind>",
       { atom_chars(Name, Cs) },
       ruleml_ind_helper(Cs),
       "</Ind>"
    ).


/*
 * ruleml_ind_helper//1 is a helper nonterminal that defines the
 * lexical grammar of individuals, storing the characters to its
 * argument Cs.
 */

ruleml_ind_helper(Cs) -->
    (  { var(Cs) } ->
       (  ( underscore(C) | big_letter(C) ) ->
          { Cs = [C | Css] },
          prolog_symbol_tail(Css)
       )
    ;  { Cs = [C | Css] },
       (  ( underscore(C) | big_letter(C) ) ->
          prolog_symbol_tail(Css)
       )
    ).


/*
 * ruleml_var//1 defines the lexical grammar of <Var>...</Var>
 * elements in RuleML/XML, and their corresponding representation in
 * Prolog. In Prolog/'$V', they are encoded as metalogical variables
 * using variable-as-'$V'-term encoding of the form '$V'(varname),
 * where varname is the exact name of the variable on the RuleML/XML
 * side.
 */

ruleml_var(Var) -->
    (  { var(Var) } ->
       list_ws("<Var>"),
       ruleml_var_contents(VarChars),
       { atom_chars(VarName, VarChars) },
       { Var = '$V'(VarName) },
       list_ws("</Var>")
    ;  { Var = '$V'(VarName) },
       "<Var>",
       { atom_chars(VarName, VarChars) },
       ruleml_var_contents(VarChars),
       "</Var>"
    ).


/*
 * The grammar of variable names within '$V' term encodings is exactly
 * that of ruleml_symbol//1. Cs is the string containing the
 * characters of the variable name/symbol.
 */

ruleml_var_contents(Cs) -->
    ruleml_symbol(Cs).


/*
 * constant_chars/3 is a helper predicate of three arguments: the type
 * of a constant, the Constant itself, and a list of characters that
 * textually represent the Constant.
 *
 * Currently, the only constant types supported are strings, numbers
 * (integers and floats), and symbols (what ISO Prolog calls atoms but
 * RuleML calls symbols).

 * In the cases of number and symbol types, (corresponding to the
 * second and third rules resp.), the predicate is invertible
 * already. In the first case, we intend either to
 *
 * 1) Create the string Constant from a pre-instantiated list of
 * Chars, or,
 *
 * 2) Instantiate a list of Chars from a pre-instantiated string
 * Constant
 *
 * based on whether Constant is instantiated.
 *
 * Note that constant_chars/3 assumes the following modes of use:
 *
 *   constant_chars(+Type, -Constant, +Chars)
 *   constant_chars(+Type, +Constant, -Chars)
 */

constant_chars(string, Chars, Chars).
constant_chars(number, Constant, Chars) :-
    catch(number_chars(Constant, Chars), _, false).
constant_chars(symbol, Constant, Chars) :-
    catch(atom_chars(Constant, Chars), _, false).


/*
 * ruleml_data//1 delegates to ruleml_data_contents//2 to determine
 * the contents of <Data> nodes, with adjoining iso:type elements.
 *
 * constant_chars/3 performs type-driven conversion between
 * Prolog/'$V' and RuleML/XML in both directions;
 * ruleml_data_contents//2 captures <Data> subelements according to
 * the grammar of RuleML/XML.
 */

ruleml_data(Name) -->
    (  { var(Name) } ->
       list_ws("<Data iso:type=\""),
       prolog_symbol(Type),
       list_ws("\">"),
       ruleml_data_contents(Type, Cs),
       { constant_chars(Type, Name, Cs) },
       list_ws("</Data>")
    ;  "<Data iso:type=\"",
       { constant_chars(Type, Name, Cs) },
       prolog_symbol(Type),
       "\">",
       ruleml_data_contents(Type, Cs),
       "</Data>"
    ).

/*
 * ruleml_data_contents//2 populates its second argument using one of
 * three subgrammars defining the data types eligible as subelements
 * of the <Data> node: numbers, strings, and symbols.
 *
 * It breaks from the '|' convention used by other union-based
 * predicates in order to provide type information needed for
 * converting from lists of characters (here denoted as Cs) to the
 * named data type in ISO Prolog. The type information is given
 * in the first argument.
 */

ruleml_data_contents(number, Cs) -->
    ruleml_number(Cs).
ruleml_data_contents(symbol, Cs) -->
    ruleml_symbol(Cs).
ruleml_data_contents(string, Cs) -->
    ruleml_string(Cs).

/*
 * ruleml_string//2 matches strings enclosed in double quotes.
 * The helper production ruleml_string_helper1//2 terminates upon discovery
 * of a second double quote character, unless it is escaped by a
 * backslash (\), in which case it is absorbed into the string.
 *
 * Explicitly checking for '\\' is only necessary when
 * ruleml_string//2 builds a list of characters CS from pre-defined
 * RuleML/XML. Otherwise, CS was obtained directly from an ISO Prolog
 * string, meaning that no escape characters were inserted after
 * conversion to a list of characters.
 */

ruleml_string(Cs) -->
    double_quote(_),
    ruleml_string_helper1(Cs).

ruleml_string_helper1(Cs) -->
    (  { var(Cs) } ->
       (  double_quote(_) ->
          { Cs = [] }
       ;  ruleml_string_char(C) ->
          (  { C == ('\\') },
             ruleml_string_escaped_char(D) ->
             { Cs = ['\\', D | Css] }
          ;  { Cs = [C | Css] }
          ),
          ruleml_string_helper1(Css)
       )
    ;  (  double_quote(_),
          { Cs = [] }
       ;  { Cs = [C | Css] },
          ruleml_string_char(C) ->
          ruleml_string_helper1(Css)
       )
    ).

/*
 * ruleml_string_escaped_char//1 defines single characters
 * escaped by backslash in ISO Prolog strings.
 */
ruleml_string_escaped_char('"') --> "\"".

/*
 * The first argument of ruleml_string_char//2 is a character that may
 * appear in an ISO Prolog string. The list of characters appearing on
 * the right hand side denotes the rendering of that character when
 * printed as the leaf of a <Data> node.
 *
 * See 6.5 of the ISO Prolog standard for the formal definition of the
 * string grammar (https://www.iso.org/standard/21413.html).
 */

ruleml_string_char('"') --> "\\\"".
ruleml_string_char('\\') --> [\].
ruleml_string_char('#') --> "#".
ruleml_string_char('$') --> "$".
ruleml_string_char('&') --> "&".
ruleml_string_char('*') --> "*".
ruleml_string_char('+') --> "+".
ruleml_string_char('-') --> "-".
ruleml_string_char('.') --> ".".
ruleml_string_char('/') --> "/".
ruleml_string_char(':') --> ":".
ruleml_string_char('<') --> "<".
ruleml_string_char('>') --> ">".
ruleml_string_char('?') --> "?".
ruleml_string_char('@') --> "@".
ruleml_string_char('^') --> "^".
ruleml_string_char('~') --> "~".
ruleml_string_char('!') --> "!".
ruleml_string_char('(') --> "(".
ruleml_string_char(')') --> ")".
ruleml_string_char(',') --> ",".
ruleml_string_char(';') --> ";".
ruleml_string_char('[') --> "[".
ruleml_string_char(']') --> "]".
ruleml_string_char('{') --> "{".
ruleml_string_char('}') --> "}".
ruleml_string_char('|') --> "|".
ruleml_string_char('%') --> "%".
ruleml_string_char(' ') --> " ".
ruleml_string_char('\x0b\') --> "\x0b\".
ruleml_string_char('\x0c\') --> "\x0c\".
ruleml_string_char('\t') --> "\t".
ruleml_string_char('\n') --> "\n".
ruleml_string_char('\'') --> "'".
ruleml_string_char(C) -->
    big_letter(C) | small_letter(C) | digit(C).

/*
 * ruleml_number//1 parses integers and floats, the amalgamated
 * grammar of which is expressed somewhat in the regular expression
 *
 * [+-0-9]?[0-9]*(\.)?[0-9]*
 *
 * This regular expressions cannot stipulate the constraint that at
 * least one digit is required on either side of the decimal point, if
 * there is one.
 *
 * The subgrammars ruleml_number_1//1 and ruleml_number_2//1 are used to
 * read characters that follow optional characters, like signs and the
 * decimal point, that can only appear once.
 */

ruleml_number(Cs) -->
    (  { var(Cs) } ->
       (  ( sign(C) | digit(C) ) ->
          { Cs = [C | Css] },
          ruleml_number_1(Css)
       ;  decimal_point(C) ->
          { Cs = [C | Css] },
          ruleml_number_2(Css)
       )
    ;  { Cs = [C | Css] },
       (  ( sign(C) | digit(C) ) ->
          ruleml_number_1(Css)
       ;  decimal_point(C) ->
          ruleml_number_2(Css)
       )
    ;  { Cs = [] }
    ).


ruleml_number_1(Cs) -->
    (  { var(Cs) } ->
       (  digit(C) ->
          { Cs = [C | Css] },
          ruleml_number_1(Css)
       ;  decimal_point(C) ->
          { Cs = [C | Css] },
          ruleml_number_2(Css)
       ;  { Cs = [] }
       )
    ;  { Cs = [C | Css] },
       (  digit(C) ->
          ruleml_number_1(Css)
       ;  decimal_point(C) ->
          ruleml_number_2(Css)
       )
    ;  { Cs = [] }
    ).


ruleml_number_2(Cs) -->
    (  { var(Cs) } ->
       (  digit(C) ->
          { Cs = [C | Css] },
          ruleml_number_2(Css)
       ;  { Cs = [] }
       )
    ;  { Cs = [C | Css] },
       (  digit(C) ->
          ruleml_number_2(Css)
       )
    ;  { Cs = [] }
    ).


/*
 * A reminder on terminology: the name symbol here refers to what Prolog
 * calls atoms. In RuleML, an atom refers to an atomic formula.
 *
 * With that out of the way, ruleml_symbol//1 is a lexical definition
 * of the RuleML symbol grammar, here conflated with Prolog atoms.
 */

ruleml_symbol(Cs) -->
    (  { var(Cs) } ->
       (  ( underscore(C) | small_letter(C) | big_letter(C) | digit(C) ) ->
          { Cs = [C | Css] },
          prolog_symbol_tail(Css)
       )
    ;  { Cs = [C | Css] },
       (  ( underscore(C) | small_letter(C) | big_letter(C) | digit(C) ) ->
          prolog_symbol_tail(Css)
       )
    ).


/*
 * ruleml_implies_head//2 defines the types of formulas that may
 * appear in the <then> edges of <Implies>, relating them to the heads
 * of Prolog/'$V' clauses. The formula must either be a RuleML atom,
 * or an <Equal>...</Equal> element.
 */

ruleml_implies_head(Item) -->
    ruleml_equal(Item) | ruleml_atom(Item).


/*
 * ruleml_implies//1 is another iteration of the translation pattern
 * we've seen many times. A ruleml_condition//1 defines what may
 * appear in an <if> edge, while ruleml_implies_head//1 describes what
 * may appear in <then> edges / Prolog/'$V' clause heads.
 *
 * On the Prolog/'$V' side, <Implies>...</Implies> elements are
 * represented as terms of the form (Head :- Body), where Body is a
 * comma-functored list of condition items and Head is given by
 * ruleml_implies_head//1.
 */

ruleml_implies(Rule) -->
    (  { var(Rule) } ->
       list_ws("<Implies>"),
       list_ws("<then>"),
       ruleml_implies_head(Head),
       list_ws("</then>"),
       list_ws("<if>"),
       ruleml_condition(Body),
       list_ws("</if>"),
       list_ws("</Implies>"),
       { Rule = ( Head :- Body ) }
    ;  { Rule = ( Head :- Body ) },
       "<Implies>",
       "<then>",
       ruleml_implies_head(Head),
       "</then>",
       "<if>",
       ruleml_condition(Body),
       "</if>",
       "</Implies>"
    ).


/*
 * ruleml_equal_items//1 describes the set of items allowed to appear
 * on either side of an equality using a '|' disjunction.
 */

ruleml_equal_item(EqualItem) -->
    ruleml_var(EqualItem) | ruleml_expr(EqualItem) | ruleml_ind(EqualItem) |
    ruleml_data(EqualItem) | ruleml_atom(EqualItem).


/*
 * ruleml_equal//1 is another rote application of the translation
 * pattern, applied to pairs of equality items in the order in which
 * they appear in an equality. The corresponding Prolog/'$V' term is (Left
 * = Right).
 */

ruleml_equal(Equal) -->
    (  { var(Equal) } ->
       list_ws("<Equal>"),
       ruleml_equal_item(Left),
       ruleml_equal_item(Right),
       list_ws("</Equal>"),
       { Equal = (Left = Right) }
    ;  { Equal = (Left = Right) },
       "<Equal>",
       ruleml_equal_item(Left),
       ruleml_equal_item(Right),
       "</Equal>"
    ).


/*
 * This is for parsing Prolog/'$V' atoms/RuleML symbols.  RuleML
 * symbols form a slightly larger set.
 */

prolog_symbol(Name) -->
    (  { atom(Name) } | { var(Name) } ) ->
        (  { var(Name) } ->
           prolog_symbol_(Cs),
           { atom_chars(Name, Cs) }
        ;  { atom_chars(Name, Cs) },
           prolog_symbol_(Cs)
        ).

prolog_symbol_([C|Cs]) -->
    small_letter(C),
    prolog_symbol_tail(Cs).


prolog_symbol_tail(Cs) -->
    (  { var(Cs) } ->
       (  ( underscore(C) | small_letter(C) | big_letter(C) | digit(C) | space(C) ) ->
          { Cs = [C|Css] }, prolog_symbol_tail(Css)
       ;  { Cs = [] }
       )
    ;  { Cs = [C|Css] } ->
       (  ( underscore(C) | small_letter(C) | big_letter(C) | digit(C) | space(C) ) ->
          prolog_symbol_tail(Css)
       ;  { Css = [] }
       )
    ;  { Cs = [] }
    ).

/*
 * small_letter//1, big_letter//1 and digit//1 all match single
 * characters of the named character classes. They each occupy
 * contiguous ranges of UTF-8 characters, and once matched, the ground
 * character C is checked for its membership in the range of the class
 * checked.
 */

small_letter(C) -->
    [C],
    {  a @=< C, C @=< z }.


big_letter(C) -->
    [C],
    { 'A' @=< C, C @=< 'Z' }.


digit(C) -->
    [C],
    {  '0' @=< C, C @=< '9' }.


/*
 * unfold_commas/2 and unfold_semicommas/2 are helper predicates. They
 * use the more general unfold_list/3 to unfold the contents of comma-
 * and semicolon-functored lists into regular Prolog lists.
 */

unfold_commas(Output, List) :-
    unfold_list((','), List, Output).

unfold_semicolons(Output, List) :-
    unfold_list((';'), List, Output).

/*
 * unfold_list/3 expects that Form is a functor symbol at the root of
 * the functored list Output, which is supposed to be
 * instantiated. Output is destructured with (=..)/2, with the first
 * item I bound to the head of the output list, unfold_list's second
 * argument. unfold_list/3 continues recursively until the
 * destructuring fails, placing the final value bound to Output at the
 * head of the list.
 */

unfold_list(Form, [I|Is], Output) :-
    (  Output =.. [Form, I, NewO] ->
       unfold_list(Form, Is, NewO)
    ;  Is = [], I = Output
    ).

/*
 * fold_commas/2 and fold_semicolons/2 are the inverse predicates of
 * unfold_commas/2 and unfold_semicolons/2.
 */

fold_commas(List, Output) :-
    fold_list(List, (','), Output).

fold_semicolons(List, Output) :-
    fold_list(List, (';'), Output).


/*
 * fold_list/3 is the inverse of of unfold_list/3. The "Prolog way"
 * would prefer unfold_list to act as its own inverse, but this is
 * complicated by Scryer's current lack of multi-argument indexing.
 */

fold_list([Item], _, Item).
fold_list([Item|Items], F, Form) :-
    Form =.. [F, Item, Fs],
    fold_list(Items, F, Fs).
