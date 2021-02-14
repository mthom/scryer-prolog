macro_rules! interm {
    ($n: expr) => {
        ArithmeticTerm::Interm($n)
    };
}

/* A simple macro to count the arguments in a variadic list
 * of token trees.
 */
macro_rules! count_tt {
    () => { 0 };
    ($odd:tt $($a:tt $b:tt)*) => { (count_tt!($($a)*) << 1) | 1 };
    ($($a:tt $even:tt)*) => { count_tt!($($a)*) << 1 };
}

macro_rules! functor {
    ($name:expr, $fixity:expr, [$($dt:ident($($value:expr),*)),+], [$($aux:ident),*]) => ({
        {
            #[allow(unused_variables, unused_mut)]
            let mut addendum = Heap::new();
            let arity = count_tt!($($dt) +);
            let aux_lens = [$($aux.len()),*];

            let mut result =
                vec![ HeapCellValue::NamedStr(arity, clause_name!($name), Some($fixity)),
                      $(functor_term!( $dt($($value),*), arity, aux_lens, addendum ),)+ ];

            $(
                result.extend($aux.into_iter());
            )*

            result.extend(addendum.into_iter());
            result
        }
    });
    ($name:expr, $fixity:expr, [$($dt:ident($($value:expr),*)),+]) => ({
        {
            #[allow(unused_variables, unused_mut)]
            let mut addendum = Heap::new();
            let arity = count_tt!($($dt) +);

            let mut result =
                vec![ HeapCellValue::NamedStr(arity, clause_name!($name), Some($fixity)),
                      $(functor_term!( $dt($($value),*), arity, [], addendum ),)+ ];

            result.extend(addendum.into_iter());
            result
        }
    });
    ($name:expr, [$($dt:ident($($value:expr),*)),+], [$($aux:ident),*]) => ({
        {
            #[allow(unused_variables, unused_mut)]
            let mut addendum = Heap::new();
            let arity = count_tt!($($dt) +);
            let aux_lens = [$($aux.len()),*];

            let mut result =
                vec![ HeapCellValue::NamedStr(arity, clause_name!($name), None),
                      $(functor_term!( $dt($($value),*), arity, aux_lens, addendum ),)+ ];

            $(
                result.extend($aux.into_iter());
            )*

            result.extend(addendum.into_iter());
            result
        }
    });
    ($name:expr, [$($dt:ident($($value:expr),*)),+]) => ({
        {
            use crate::machine::heap::*;

            let arity = count_tt!($($dt) +);
            #[allow(unused_variables, unused_mut)]
            let mut addendum = Heap::new();

            let mut result =
                vec![ HeapCellValue::NamedStr(arity, clause_name!($name), None),
                      $(functor_term!( $dt($($value),*), arity, [], addendum ),)+ ];

            result.extend(addendum.into_iter());
            result
        }
    });
    ($name:expr, $fixity:expr) => (
        vec![ HeapCellValue::Atom(clause_name!($name), Some($fixity)) ]
    );
    (clause_name($name:expr)) => (
        vec![ HeapCellValue::Atom($name, None) ]
    );
    ($name:expr) => (
        vec![ HeapCellValue::Atom(clause_name!($name), None) ]
    );
}

macro_rules! functor_term {
    (aux(0), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        HeapCellValue::Addr(Addr::HeapCell($arity + 1))
    });
    (aux($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        let len: usize = $aux_lens[0 .. $e].iter().sum();
        HeapCellValue::Addr(Addr::HeapCell($arity + 1 + len))
    });
    (aux($h:expr, 0), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        HeapCellValue::Addr(Addr::HeapCell($arity + $h + 1))
    });
    (aux($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        let len: usize = $aux_lens[0 .. $e].iter().sum();
        HeapCellValue::Addr(Addr::HeapCell($arity + $h + 1 + len))
    });
    (addr($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::Addr($e)
    );
    (constant($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        from_constant!($e, $h, $arity, $aux_lens, $addendum)
    );
    (constant($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        from_constant!($e, 0, $arity, $aux_lens, $addendum)
    );
    (number($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        $e.into()
    );
    (integer($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::Integer(Rc::new(Integer::from($e)))
    );
    (indexing_code_ptr($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        let stub =
            match $e {
                IndexingCodePtr::External(o) => functor!("external", [integer(o)]),
                IndexingCodePtr::Internal(o) => functor!("internal", [integer(o)]),
                IndexingCodePtr::Fail => vec![HeapCellValue::Atom(clause_name!("fail"), None)],
            };

        let len: usize = $aux_lens.iter().sum();
        let h = len + $arity + 1 + $addendum.h() + $h;

        $addendum.extend(stub.into_iter());

        HeapCellValue::Addr(Addr::HeapCell(h))
    });
    (clause_name($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::Atom($e, None)
    );
    (atom($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::Atom(clause_name!($e), None)
    );
    (value($e:expr), $arity:expr, $aux_lens:expr, $addendum: ident) => (
        $e
    );
    (string($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum: ident) => ({
        let len: usize = $aux_lens.iter().sum();
        let h = len + $arity + 1 + $addendum.h() + $h;

        $addendum.put_complete_string(&$e);

        HeapCellValue::Addr(Addr::PStrLocation(h, 0))
    });
    (boolean($e:expr), $arity:expr, $aux_lens:expr, $addendum: ident) => ({
        if $e {
            functor_term!(atom("true"), $arity, $aux_lens, $addendum)
        } else {
            functor_term!(atom("false"), $arity, $aux_lens, $addendum)
        }
    });
    ($e:expr, $arity:expr, $aux_lens:expr, $addendum:ident) => (
        $e
    );
}

macro_rules! from_constant {
    ($e:expr, $over_h:expr, $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        match $e {
            &Constant::Atom(ref name, ref op) => {
                HeapCellValue::Atom(name.clone(), op.clone())
            }
            &Constant::Char(c) => {
                HeapCellValue::Addr(Addr::Char(c))
            }
            &Constant::Fixnum(n) => {
                HeapCellValue::Addr(Addr::Fixnum(n))
            }
            &Constant::Integer(ref n) => {
                HeapCellValue::Integer(n.clone())
            }
            &Constant::Rational(ref r) => {
                HeapCellValue::Rational(r.clone())
            }
            &Constant::Float(f) => {
                HeapCellValue::Addr(Addr::Float(f))
            }
            &Constant::String(ref s) => {
                let len: usize = $aux_lens.iter().sum();
                let h = len + $arity + 1 + $addendum.h() + $over_h;

                $addendum.put_complete_string(&s);

                HeapCellValue::Addr(Addr::PStrLocation(h, 0))
            }
            &Constant::Usize(u) => {
                HeapCellValue::Addr(Addr::Usize(u))
            }
            &Constant::EmptyList => {
                HeapCellValue::Addr(Addr::EmptyList)
            }
        }
    })
}

macro_rules! is_atom {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsAtom($r)), 1, 0)
    };
}

macro_rules! is_atomic {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsAtomic($r)), 1, 0)
    };
}

macro_rules! is_integer {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsInteger($r)), 1, 0)
    };
}

macro_rules! is_compound {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsCompound($r)), 1, 0)
    };
}

macro_rules! is_float {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsFloat($r)), 1, 0)
    };
}

macro_rules! is_rational {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsRational($r)), 1, 0)
    };
}

macro_rules! is_number {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsNumber($r)), 1, 0)
    };
}

macro_rules! is_nonvar {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsNonVar($r)), 1, 0)
    };
}

macro_rules! is_var {
    ($r:expr) => {
        call_clause!(ClauseType::Inlined(InlinedClauseType::IsVar($r)), 1, 0)
    };
}

macro_rules! call_clause {
    ($ct:expr, $arity:expr, $pvs:expr) => {
        Line::Control(ControlInstruction::CallClause(
            $ct, $arity, $pvs, false, false,
        ))
    };
    ($ct:expr, $arity:expr, $pvs:expr, $lco:expr) => {
        Line::Control(ControlInstruction::CallClause(
            $ct, $arity, $pvs, $lco, false,
        ))
    };
}

macro_rules! call_clause_by_default {
    ($ct:expr, $arity:expr, $pvs:expr) => {
        Line::Control(ControlInstruction::CallClause(
            $ct, $arity, $pvs, false, true,
        ))
    };
    ($ct:expr, $arity:expr, $pvs:expr, $lco:expr) => {
        Line::Control(ControlInstruction::CallClause(
            $ct, $arity, $pvs, $lco, true,
        ))
    };
}

macro_rules! proceed {
    () => {
        Line::Control(ControlInstruction::Proceed)
    };
}

macro_rules! is_call {
    ($r:expr, $at:expr) => {
        call_clause!(ClauseType::BuiltIn(BuiltInClauseType::Is($r, $at)), 2, 0)
    };
}

macro_rules! is_call_by_default {
    ($r:expr, $at:expr) => {
        call_clause_by_default!(ClauseType::BuiltIn(BuiltInClauseType::Is($r, $at)), 2, 0)
    };
}

macro_rules! set_cp {
    ($r:expr) => {
        call_clause!(ClauseType::System(SystemClauseType::SetCutPoint($r)), 1, 0)
    };
}

macro_rules! succeed {
    () => {
        call_clause!(ClauseType::System(SystemClauseType::Succeed), 0, 0)
    };
}

macro_rules! fail {
    () => {
        call_clause!(ClauseType::System(SystemClauseType::Fail), 0, 0)
    };
}

macro_rules! compare_number_instr {
    ($cmp: expr, $at_1: expr, $at_2: expr) => {{
        let ct = ClauseType::Inlined(InlinedClauseType::CompareNumber($cmp, $at_1, $at_2));
        call_clause!(ct, 2, 0)
    }};
}

macro_rules! jmp_call {
    ($arity:expr, $offset:expr, $pvs:expr) => {
        Line::Control(ControlInstruction::JmpBy($arity, $offset, $pvs, false))
    };
}

macro_rules! return_from_clause {
    ($lco:expr, $machine_st:expr) => {{
        if let CodePtr::VerifyAttrInterrupt(_) = $machine_st.p {
            return Ok(());
        }

        if $lco {
            $machine_st.p = CodePtr::Local($machine_st.cp);
        } else {
            $machine_st.p += 1;
        }

        Ok(())
    }};
}

macro_rules! dir_entry {
    ($idx:expr) => {
        LocalCodePtr::DirEntry($idx)
    };
}

macro_rules! index_store {
    ($code_dir:expr, $op_dir:expr, $modules:expr) => {
        IndexStore {
            code_dir: $code_dir,
            extensible_predicates: ExtensiblePredicates::new(),
            local_extensible_predicates: LocalExtensiblePredicates::new(),
            global_variables: GlobalVarDir::new(),
            meta_predicates: MetaPredicateDir::new(),
            modules: $modules,
            op_dir: $op_dir,
            streams: StreamDir::new(),
            stream_aliases: StreamAliasDir::new(),
        }
    };
}

macro_rules! put_constant {
    ($lvl:expr, $cons:expr, $r:expr) => {
        QueryInstruction::PutConstant($lvl, $cons, $r)
    };
}

macro_rules! get_level_and_unify {
    ($r: expr) => {
        Line::Cut(CutInstruction::GetLevelAndUnify($r))
    };
}

/*
macro_rules! unwind_protect {
    ($e: expr, $protected: expr) => {
        match $e {
            Err(e) => {
                $protected;
                return Err(e);
            }
            _ => {}
        }
    };
}
*/
/*
macro_rules! discard_result {
    ($f: expr) => {
        match $f {
            _ => (),
        }
    };
}
*/
macro_rules! ar_reg {
    ($r: expr) => {
        ArithmeticTerm::Reg($r)
    };
}

macro_rules! atom_from {
    ($self:expr, $e:expr) => {
        match $e {
            Addr::Con(h) if $self.heap.atom_at(h) => {
                match &$self.heap[h] {
                    HeapCellValue::Atom(ref atom, _) => {
                        atom.clone()
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            Addr::Char(c) => {
                clause_name!(c.to_string(), $self.atom_tbl)
            }
            _ => {
                unreachable!()
            }
        }
    }
}

macro_rules! try_or_fail {
    ($s:expr, $e:expr) => {{
        match $e {
            Ok(val) => val,
            Err(msg) => {
                $s.throw_exception(msg);
                return;
            }
        }
    }};
}
