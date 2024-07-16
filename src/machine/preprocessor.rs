use crate::atom_table::*;
use crate::codegen::CodeGenSettings;
use crate::forms::*;
use crate::instructions::*;
use crate::machine::disjuncts::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::machine::CodeIndex;
use crate::parser::ast::*;
use crate::types::*;

use fxhash::FxBuildHasher;
use indexmap::IndexMap;
use indexmap::IndexSet;

use std::convert::TryFrom;
pub(crate) fn to_op_decl(prec: u16, spec: OpDeclSpec, name: Atom) -> OpDecl {
    OpDecl::new(OpDesc::build_with(prec, spec), name)
}

pub(crate) fn to_op_decl_spec(spec: Atom) -> Result<OpDeclSpec, CompilationError> {
    OpDeclSpec::try_from(spec).map_err(|_err| {
        CompilationError::InvalidDirective(DirectiveError::InvalidOpDeclSpecValue(spec))
    })
}

fn setup_op_decl(term: &FocusedHeapRefMut) -> Result<OpDecl, CompilationError> {
    let (focus, _cell) = subterm_index(term.heap, term.focus);

    let name = match term.name(focus+3) {
        Some(name) => name,
        None => return Err(CompilationError::InconsistentEntry),
    };

    let spec = match term.name(focus+2) {
        Some(name) => name,
        None => return Err(CompilationError::InconsistentEntry),
    };

    let prec = read_heap_cell!(term.deref_loc(focus+1),
        (HeapCellValueTag::Fixnum, n) => {
            match u16::try_from(n.get_num()) {
                Ok(n) if n <= 1200 => n,
                _ => return Err(CompilationError::InconsistentEntry),
            }
        }
        _ => {
            return Err(CompilationError::InconsistentEntry);
        }
    );

    if name == "[]" || name == "{}" {
        return Err(CompilationError::InvalidDirective(
            DirectiveError::ShallNotCreate(name),
        ));
    }

    if name == "," {
        return Err(CompilationError::InvalidDirective(
            DirectiveError::ShallNotModify(name),
        ));
    }

    if name == "|" && (prec < 1001 || !spec.is_infix()) {
        return Err(CompilationError::InvalidDirective(
            DirectiveError::ShallNotCreate(name),
        ));
    }

    Ok(to_op_decl(prec, spec, name))
}

fn setup_predicate_indicator(term: &FocusedHeapRefMut) -> Result<PredicateKey, CompilationError> {
    let name_opt = term.name(term.focus);
    let arity = term.arity(term.focus);

    if let (Some(atom!("/") | atom!("//")), 2) = (name_opt, arity) {
        let arity_loc = term.nth_arg(term.focus, 2).unwrap();

        let arity = match Number::try_from(term.deref_loc(arity_loc)) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            Ok(Number::Integer(n)) => (&*n).try_into().ok(),
            _ => None,
        }
        .ok_or(CompilationError::InvalidModuleExport)?;

        let name_loc = term.nth_arg(term.focus, 1).unwrap();
        let name = term
            .name(name_loc)
            .ok_or(CompilationError::InvalidModuleExport)?;

        if name_opt == Some(atom!("/")) {
            Ok((name, arity))
        } else {
            Ok((name, arity + 2))
        }
    } else {
        Err(CompilationError::InvalidModuleExport)
    }
}

fn setup_module_export(term: &FocusedHeapRefMut) -> Result<ModuleExport, CompilationError> {
    setup_predicate_indicator(term)
        .map(ModuleExport::PredicateKey)
        .or_else(|_| {
            let name_opt = term.name(term.focus);
            let arity = term.arity(term.focus);

            if let (Some(atom!("op")), 3) = (name_opt, arity) {
                Ok(ModuleExport::OpDecl(setup_op_decl(term)?))
            } else {
                Err(CompilationError::InvalidModuleDecl)
            }
        })
}

/* TODO: should be unnecessary now.

pub(crate) fn build_rule_body(vars: &[Term], body_term: Term) -> Term {
    let head_term = Term::Clause(Cell::default(), atom!(""), vars.to_vec());
    let rule = vec![head_term, body_term];

    Term::Clause(Cell::default(), atom!(":-"), rule)
}
*/

pub(super) fn setup_module_export_list(
    term: FocusedHeapRefMut,
) -> Result<Vec<ModuleExport>, CompilationError> {
    let mut exports = vec![];
    let mut focus = term.focus;

    loop {
	read_heap_cell!(term.heap[focus],
	    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
		if h == focus {
		    break;
		} else {
		    focus = h;
		}
	    }
	    (HeapCellValueTag::Lis, l) => {
		let term = FocusedHeapRefMut {
		    heap: term.heap,
		    focus: l,
		};
		exports.push(setup_module_export(&term)?);

		focus = l + 1;
	    }
            (HeapCellValueTag::Atom, (name, _arity)) => {
		if name == atom!("[]") {
		    return Ok(exports);
		} else {
		    break;
		}
	    }
	    _ => {
		break;
	    }
	);
    }

    Err(CompilationError::InvalidModuleDecl)
}

fn setup_module_decl(term: FocusedHeapRefMut) -> Result<ModuleDecl, CompilationError> {
    let name = term
        .name(term.focus + 1)
        .ok_or(CompilationError::InvalidModuleDecl)?;
    let export_list = FocusedHeapRefMut {
        heap: term.heap,
        focus: term.focus + 2,
    };
    let exports = setup_module_export_list(export_list)?;

    Ok(ModuleDecl { name, exports })
}

fn setup_use_module_decl(term: &FocusedHeapRefMut) -> Result<ModuleSource, CompilationError> {
    read_heap_cell!(term.deref_loc(term.focus+1),
        (HeapCellValueTag::Str, s) => {
            let (name, arity) = cell_as_atom_cell!(term.heap[s]).get_name_and_arity();

            if (name, arity) == (atom!("library"), 1) {
                read_heap_cell!(term.deref_loc(s+1),
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        if arity == 0 {
                            return Ok(ModuleSource::Library(name));
                        }
                    }
                    _ => {
                    }
                )
            }

            return Err(CompilationError::InvalidModuleDecl);
        }
        (HeapCellValueTag::Atom, (name, arity)) => {
            if arity == 0 {
                Ok(ModuleSource::File(name))
            } else {
                Err(CompilationError::InvalidUseModuleDecl)
            }
        }
        _ => {
            Err(CompilationError::InvalidUseModuleDecl)
        }
    )
}

type UseModuleExport = (ModuleSource, IndexSet<ModuleExport>);

fn setup_qualified_import(term: FocusedHeapRefMut) -> Result<UseModuleExport, CompilationError> {
    let module_src = setup_use_module_decl(&term)?;
    let mut exports = IndexSet::new();

    let mut focus = term.focus + 2;

    while let HeapCellValueTag::Lis = term.heap[focus].get_tag() {
        focus = term.heap[focus].get_value() as usize;

        let term = FocusedHeapRefMut {
            heap: term.heap,
            focus,
        };
        exports.insert(setup_module_export(&term)?);

        focus = focus + 1;
    }

    if term.heap[focus] == empty_list_as_cell!() {
        Ok((module_src, exports))
    } else {
        Err(CompilationError::InvalidModuleDecl)
    }
}

/*
 * setup_meta_predicate tries to extract meta-predicate information
 * from an appropriately formed declaration
 *
 * :- meta_predicate maplist(:, ?, ?).
 *
 * indicating that, for each QueryTerm call to maplist/3, the first
 * argument is to be expanded with the call resolution ((:)/2)
 * operator, the first argument of which is the name of the host
 * module, as an atom. For example,
 *
 * p(X) :- maplist(X, [a,b,c], Result).
 *
 * If p/2 is defined in a module named "mod", the call is expanded to
 *
 * maplist(mod:X, [a,b,c], Result).
 *
 * before the predicate is compiled to WAM instructions.
 *
 * If the term bound to X -- the predicate to be called -- is
 * qualified with (:)/2 already, the innermost qualifier is used for
 * call resolution.
 *
 * The three arguments returned by a successful call are the module name,
 * predicate name, and the list of meta-specs, one for each predicate argument.
 *
 * The module name might be used to specify intra-module meta-predicates whose
 * module is not yet defined. There are several examples of this
 * contained in src/lib/ops_and_meta_predicates.pl, which is loaded before
 * src/lib/builtins.pl.
 *
 * Meta-specs have three forms:
 *
 * (:)  (the argument should be expanded with (:)/2 as described above)
 * +    (mode declarations under the mode syntax, which currently have no effect)
 * -
 * ?
 */

fn setup_meta_predicate<'a, LS: LoadState<'a>>(
    term: FocusedHeapRefMut,
    loader: &mut Loader<'a, LS>,
) -> Result<(Atom, Atom, Vec<MetaSpec>), CompilationError> {
    fn get_meta_specs(
        term: FocusedHeapRefMut,
        arity: usize,
    ) -> Result<Vec<MetaSpec>, CompilationError> {
        let mut meta_specs = vec![];

        for meta_spec_loc in term.focus + 1..term.focus + arity + 1 {
            read_heap_cell!(term.deref_loc(meta_spec_loc),
                (HeapCellValueTag::Atom, (meta_spec, arity)) => {
                    debug_assert_eq!(arity, 0);

                    let meta_spec = match meta_spec {
                        atom!("+") => MetaSpec::Plus,
                        atom!("-") => MetaSpec::Minus,
                        atom!("?") => MetaSpec::Either,
                        atom!(":") => MetaSpec::Colon,
                        _ => return Err(CompilationError::InvalidMetaPredicateDecl),
                    };

                    meta_specs.push(meta_spec);
                }
                (HeapCellValueTag::Fixnum, n) => {
                    match usize::try_from(n.get_num()) {
                        Ok(n) if n <= MAX_ARITY => {
                            meta_specs.push(MetaSpec::RequiresExpansionWithArgument(n));
                        }
                        _ => {
                            return Err(CompilationError::InvalidMetaPredicateDecl);
                        }
                    }
                }
                _ => {
                    return Err(CompilationError::InvalidMetaPredicateDecl);
                }
            );
        }

        Ok(meta_specs)
    }

    read_heap_cell!(term.deref_loc(term.focus+1),
        (HeapCellValueTag::Str, s) => {
            let (name, arity) = cell_as_atom_cell!(term.heap[s]).get_name_and_arity();

            match (name, arity) {
                (atom!(":"), 2) => {
                    let module_name = term.heap[s+1];
                    let spec = term.heap[s+2];

                    read_heap_cell!(module_name,
                        (HeapCellValueTag::Atom, (module_name, arity)) => {
                            if arity == 0 {
                                read_heap_cell!(spec,
                                    (HeapCellValueTag::Str, s) => {
                                        let (name, arity) = cell_as_atom_cell!(term.heap[s])
                                            .get_name_and_arity();

                                        let term = FocusedHeapRefMut { heap: term.heap, focus: s };
                                        return Ok((module_name, name, get_meta_specs(term, arity)?));
                                    }
                                    _ => {
                                    }
                                );
                            } else {
                                return Err(CompilationError::InvalidMetaPredicateDecl);
                            }
                        }
                        _ => {
                        }
                    );
                }
                _ => {
                    let term = FocusedHeapRefMut { heap: term.heap, focus: s };
                    let module_name = loader.payload.compilation_target.module_name();
                    return Ok((module_name, name, get_meta_specs(term, arity)?));
                }
            }

            Err(CompilationError::InvalidMetaPredicateDecl)
        }
        _ => {
            Err(CompilationError::InvalidMetaPredicateDecl)
        }
    )
}

pub(super) fn setup_declaration<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    term: FocusedHeapRefMut,
) -> Result<Declaration, CompilationError> {
    let mut focus = term.focus;

    loop {
        read_heap_cell!(term.heap[focus],
            (HeapCellValueTag::Atom, (name, arity)) => {
                let term = FocusedHeapRefMut { heap: term.heap, focus };

                return match (name, arity) {
                    (atom!("dynamic"), 1) => {
                        let (name, arity) = setup_predicate_indicator(&term)?;
                        Ok(Declaration::Dynamic(name, arity))
                    }
                    (atom!("module"), 2) => {
                        Ok(Declaration::Module(setup_module_decl(term)?))
                    }
                    (atom!("op"), 3) => {
                        Ok(Declaration::Op(setup_op_decl(&term)?))
                    }
                    (atom!("non_counted_backtracking"), 1) => {
                        let focus = term.nth_arg(term.focus, 1).unwrap();
                        let (name, arity) = setup_predicate_indicator(&FocusedHeapRefMut { heap: term.heap, focus })?;
                        Ok(Declaration::NonCountedBacktracking(name, arity))
                    }
                    (atom!("use_module"), 1) => Ok(Declaration::UseModule(setup_use_module_decl(&term)?)),
                    (atom!("use_module"), 2) => {
                        let (name, exports) = setup_qualified_import(term)?;

                        Ok(Declaration::UseQualifiedModule(name, exports))
                    }
                    (atom!("meta_predicate"), 1) => {
                        let (module_name, name, meta_specs) = setup_meta_predicate(term, loader)?;
                        Ok(Declaration::MetaPredicate(module_name, name, meta_specs))
                    }
                    _ => Err(CompilationError::InvalidDirective(
                        DirectiveError::InvalidDirective(name, arity)
                    ))
                };
            }
            (HeapCellValueTag::Str, s) => {
                focus = s;
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                if focus != h {
                    focus = h;
                } else {
                    return Err(CompilationError::InvalidDirective(
                        DirectiveError::ExpectedDirective(heap_loc_as_cell!(h)),
                    ));
                }
            }
            _ => {
                return Err(CompilationError::InvalidDirective(
                    DirectiveError::ExpectedDirective(term.heap[focus])
                ));
            }
        );
    }
}

fn build_meta_predicate_clause<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    module_name: Atom,
    arity: usize,
    term: &FocusedHeapRefMut,
    meta_specs: Vec<MetaSpec>,
) -> IndexMap<usize, CodeIndex, FxBuildHasher> {
    let mut index_ptrs = IndexMap::with_hasher(FxBuildHasher::default());

    for (subterm_loc, meta_spec) in (term.focus + 1..term.focus + arity + 1).zip(meta_specs) {
        if let MetaSpec::RequiresExpansionWithArgument(supp_args) = meta_spec {
            if let Some(name) = term.name(subterm_loc) {
                if name == atom!("$call") {
                    continue;
                }

                let arity = term.arity(subterm_loc);

                struct QualifiedNameInfo {
                    module_name: Atom,
                    name: Atom,
                    qualified_term_loc: usize,
                }

                fn get_qualified_name(
                    term: &FocusedHeapRefMut,
                    module_term_loc: usize,
                    qualified_term_loc: usize,
                ) -> Option<QualifiedNameInfo> {
                    let (module_term_loc, _) = subterm_index(term.heap, module_term_loc);
                    let (qualified_term_loc, _) = subterm_index(term.heap, qualified_term_loc);

                    read_heap_cell!(term.heap[module_term_loc],
                        (HeapCellValueTag::Atom, (module_name, arity)) => {
                            if arity == 0 {
                                if let Some(name) = term.name(qualified_term_loc) {
                                    return Some(QualifiedNameInfo {
                                        module_name,
                                        name,
                                        qualified_term_loc,
                                    });
                                }
                            }
                        }
                        _ => {}
                    );

                    None
                }

                let (subterm_loc, _) = subterm_index(term.heap, subterm_loc);

                let subterm_arity = term.arity(subterm_loc);
                let subterm_name_opt = term.name(subterm_loc);

                let (module_name, key, term_loc) =
                    if subterm_name_opt == Some(atom!(":")) && subterm_arity == 2 {
                        debug_assert_eq!(term.heap[subterm_loc].get_tag(), HeapCellValueTag::Atom);

                        match get_qualified_name(term, subterm_loc + 1, subterm_loc + 2) {
                            Some(QualifiedNameInfo {
                                module_name,
                                name,
                                qualified_term_loc,
                            }) => (
                                module_name,
                                (name, term.arity(qualified_term_loc) + supp_args),
                                qualified_term_loc,
                            ),
                            None => {
                                continue;
                            }
                        }
                    } else {
                        (module_name, (name, arity + supp_args), subterm_loc)
                    };

                if let Some(index_ptr) = fetch_index_ptr(term.heap, key.1, term_loc) {
                    index_ptrs.insert(term_loc, index_ptr);
                    continue;
                }

                index_ptrs.insert(
                    term_loc,
                    loader.get_or_insert_qualified_code_index(module_name, key),
                );
            }
        }
    }

    index_ptrs
}

#[inline]
pub(super) fn clause_to_query_term<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    key: PredicateKey,
    terms: FocusedHeapRefMut,
    term: HeapCellValue,
    call_policy: CallPolicy,
) -> QueryClause {
    // supplementary code vector indices are unnecessary for
    // root-level clauses.
    blunt_index_ptr(terms.heap, key, terms.focus);

    let mut ct = loader.get_clause_type(key.0, key.1);

    if let ClauseType::Named(arity, name, idx) = ct {
        if let Some(meta_specs) = loader.get_meta_specs(name, arity).cloned() {
            let module_name = loader.payload.compilation_target.module_name();
            let code_indices =
                build_meta_predicate_clause(loader, module_name, arity, &terms, meta_specs);

            return QueryClause {
                ct: ClauseType::Named(key.1, key.0, idx),
                arity,
                term,
                code_indices,
                call_policy,
            };
        }

        ct = ClauseType::Named(key.1, key.0, idx);
    }

    QueryClause {
        ct,
        arity: key.1,
        term,
        code_indices: IndexMap::with_hasher(FxBuildHasher::default()),
        call_policy,
    }
}

#[inline]
pub(super) fn qualified_clause_to_query_term<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    key: PredicateKey,
    module_name: Atom,
    terms: FocusedHeapRefMut,
    term: HeapCellValue,
    call_policy: CallPolicy,
) -> QueryClause {
    // supplementary code vector indices are unnecessary for
    // root-level clauses.
    blunt_index_ptr(terms.heap, key, terms.focus);

    let mut ct = loader.get_qualified_clause_type(module_name, key.0, key.1);

    if let ClauseType::Named(arity, name, idx) = ct {
        if let Some(meta_specs) = loader.get_meta_specs(name, arity).cloned() {
            let code_indices =
                build_meta_predicate_clause(loader, module_name, arity, &terms, meta_specs);

            return QueryClause {
                ct: ClauseType::Named(key.1, key.0, idx),
                arity,
                term,
                code_indices,
                call_policy,
            };
        }

        ct = ClauseType::Named(key.1, key.0, idx);
    }

    QueryClause {
        ct,
        arity: key.1,
        term,
        code_indices: IndexMap::with_hasher(FxBuildHasher::default()),
        call_policy,
    }
}

#[derive(Debug)]
pub(crate) struct Preprocessor {
    settings: CodeGenSettings,
}

impl Preprocessor {
    pub(super) fn new(settings: CodeGenSettings) -> Self {
        Preprocessor { settings }
    }

    pub fn setup_fact(
        &mut self,
        mut term: FocusedHeap,
    ) -> Result<(Fact, VarData), CompilationError> {
        if term.name(term.focus).is_some() {
            let classifier = VariableClassifier::new(self.settings.default_call_policy());
            let var_data = classifier.classify_fact(&mut term)?;

            Ok((Fact { term }, var_data))
        } else {
            Err(CompilationError::InadmissibleFact)
        }
    }

    fn setup_rule<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        mut term: FocusedHeap,
    ) -> Result<(Rule, VarData), CompilationError> {
        let classifier = VariableClassifier::new(self.settings.default_call_policy());
        let (clauses, var_data) = classifier.classify_rule(loader, &mut term)?;
        let head_loc = term.nth_arg(term.focus, 1).unwrap();

        if term.name(head_loc).is_some() {
            Ok((Rule { term, clauses }, var_data))
        } else {
            Err(CompilationError::InvalidRuleHead)
        }
    }

    pub(super) fn try_term_to_tl<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: FocusedHeap,
    ) -> Result<TopLevel, CompilationError> {
        let name = term.name(term.focus);
        let arity = term.arity(term.focus);

        match (name, arity) {
            (Some(atom!(":-")), 2) => {
                let (rule, var_data) = self.setup_rule(loader, term)?;
                Ok(TopLevel::Rule(rule, var_data))
            }
            _ => {
                let (fact, var_data) = self.setup_fact(term)?;
                Ok(TopLevel::Fact(fact, var_data))
            }
        }
    }
}
