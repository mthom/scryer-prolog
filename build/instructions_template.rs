// use crate::atom_table::*;
// use crate::machine::machine_indices::*;
// use crate::types::*;
//

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens, TokenStreamExt};
use strum_macros::{EnumDiscriminants, EnumProperty, EnumString};
use syn::*;
use to_syn_value_derive::ToDeriveInput;

/*
 * This crate exists to generate the Instruction enum in
 * src/instructions.rs and its adjoining impl functions. The types
 * defined in it are empty and serve only as schema for the generation
 * of Instruction. They mimic most of the structure of the previous
 * Line instruction type. The strum crate is used to provide reflection
 * on each of the node types to the tree walker.
*/

use std::any::*;
use std::rc::Rc;
use std::str::FromStr;

struct ArithmeticTerm;
struct Atom;
struct CodeIndex;
struct Death;
struct HeapCellValue;
struct IndexingLine;
struct Level;
// struct Literal;
struct NextOrFail;
struct RegType;

#[allow(clippy::enum_variant_names)]
#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum CompareNumber {
    #[strum_discriminants(strum(props(Arity = "2", Name = ">")))]
    NumberGreaterThan(ArithmeticTerm, ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = "<")))]
    NumberLessThan(ArithmeticTerm, ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = ">=")))]
    NumberGreaterThanOrEqual(ArithmeticTerm, ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = "=<")))]
    NumberLessThanOrEqual(ArithmeticTerm, ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = "=\\=")))]
    NumberNotEqual(ArithmeticTerm, ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = "=:=")))]
    NumberEqual(ArithmeticTerm, ArithmeticTerm),
}

#[allow(clippy::enum_variant_names)]
#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum CompareTerm {
    #[strum_discriminants(strum(props(Arity = "2", Name = "@<")))]
    TermLessThan,
    #[strum_discriminants(strum(props(Arity = "2", Name = "@=<")))]
    TermLessThanOrEqual,
    #[strum_discriminants(strum(props(Arity = "2", Name = "@>=")))]
    TermGreaterThanOrEqual,
    #[strum_discriminants(strum(props(Arity = "2", Name = "@>")))]
    TermGreaterThan,
    #[strum_discriminants(strum(props(Arity = "2", Name = "==")))]
    TermEqual,
    #[strum_discriminants(strum(props(Arity = "2", Name = "\\==")))]
    TermNotEqual,
}

#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum ClauseType {
    BuiltIn(BuiltInClauseType),
    #[strum_discriminants(strum(props(Arity = "arity", Name = "$call")))]
    CallN(usize),
    Inlined(InlinedClauseType),
    #[strum_discriminants(strum(props(Arity = "arity", Name = "call_named")))]
    Named(usize, Atom, CodeIndex), // name, arity, index.
    System(SystemClauseType),
}

#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum BuiltInClauseType {
    #[strum_discriminants(strum(props(Arity = "1", Name = "acyclic_term")))]
    AcyclicTerm,
    #[strum_discriminants(strum(props(Arity = "3", Name = "arg")))]
    Arg,
    #[strum_discriminants(strum(props(Arity = "3", Name = "compare")))]
    Compare,
    CompareTerm(CompareTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = "copy_term")))]
    CopyTerm,
    #[strum_discriminants(strum(props(Arity = "3", Name = "functor")))]
    Functor,
    #[strum_discriminants(strum(props(Arity = "1", Name = "ground")))]
    Ground,
    #[strum_discriminants(strum(props(Arity = "2", Name = "is")))]
    Is(RegType, ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_number")))]
    GetNumber(ArithmeticTerm),
    #[strum_discriminants(strum(props(Arity = "2", Name = "keysort")))]
    KeySort,
    #[strum_discriminants(strum(props(Arity = "2", Name = "sort")))]
    Sort,
}

#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum InlinedClauseType {
    CompareNumber(CompareNumber),
    #[strum_discriminants(strum(props(Arity = "1", Name = "atom")))]
    IsAtom(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "atomic")))]
    IsAtomic(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "compound")))]
    IsCompound(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "integer")))]
    IsInteger(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "number")))]
    IsNumber(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "rational")))]
    IsRational(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "float")))]
    IsFloat(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "nonvar")))]
    IsNonVar(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "var")))]
    IsVar(RegType),
}

#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum ReplCodePtr {
    #[strum_discriminants(strum(props(Arity = "4", Name = "$add_discontiguous_predicate")))]
    AddDiscontiguousPredicate,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$add_dynamic_predicate")))]
    AddDynamicPredicate,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$add_multifile_predicate")))]
    AddMultifilePredicate,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$add_goal_expansion_clause")))]
    AddGoalExpansionClause,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$add_term_expansion_clause")))]
    AddTermExpansionClause,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$add_in_situ_filename_module")))]
    AddInSituFilenameModule,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$clause_to_evacuable")))]
    ClauseToEvacuable,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$scoped_clause_to_evacuable")))]
    ScopedClauseToEvacuable,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$conclude_load")))]
    ConcludeLoad,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$declare_module")))]
    DeclareModule,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$load_compiled_library")))]
    LoadCompiledLibrary,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$prolog_lc_source")))]
    LoadContextSource,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$prolog_lc_file")))]
    LoadContextFile,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$prolog_lc_dir")))]
    LoadContextDirectory,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$prolog_lc_module")))]
    LoadContextModule,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$prolog_lc_stream")))]
    LoadContextStream,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$pop_load_context")))]
    PopLoadContext,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$pop_load_state_payload")))]
    PopLoadStatePayload,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$push_load_state_payload")))]
    PushLoadStatePayload,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$push_load_context")))]
    PushLoadContext,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$use_module")))]
    UseModule,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$built_in_property")))]
    BuiltInProperty,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$meta_predicate_property")))]
    MetaPredicateProperty,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$multifile_property")))]
    MultifileProperty,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$discontiguous_property")))]
    DiscontiguousProperty,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$dynamic_property")))]
    DynamicProperty,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$abolish_clause")))]
    AbolishClause,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$asserta")))]
    Asserta,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$assertz")))]
    Assertz,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$retract_clause")))]
    Retract,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$is_consistent_with_term_queue")))]
    IsConsistentWithTermQueue,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$flush_term_queue")))]
    FlushTermQueue,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$remove_module_exports")))]
    RemoveModuleExports,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$add_non_counted_backtracking")))]
    AddNonCountedBacktracking,
}

#[allow(clippy::upper_case_acronyms)]
#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum SystemClauseType {
    #[strum_discriminants(strum(props(Arity = "2", Name = "$atom_chars")))]
    AtomChars,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$atom_codes")))]
    AtomCodes,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$atom_length")))]
    AtomLength,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$bind_from_register")))]
    BindFromRegister,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$call_continuation")))]
    CallContinuation,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$char_code")))]
    CharCode,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$char_type")))]
    CharType,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$chars_to_number")))]
    CharsToNumber,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$codes_to_number")))]
    CodesToNumber,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$copy_term_without_attr_vars")))]
    CopyTermWithoutAttrVars,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$check_cp")))]
    CheckCutPoint,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$close")))]
    Close,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$copy_to_lh")))]
    CopyToLiftedHeap,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$create_partial_string")))]
    CreatePartialString,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$current_hostname")))]
    CurrentHostname,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$current_input")))]
    CurrentInput,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$current_output")))]
    CurrentOutput,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$directory_files")))]
    DirectoryFiles,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$file_size")))]
    FileSize,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$file_exists")))]
    FileExists,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$directory_exists")))]
    DirectoryExists,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$directory_separator")))]
    DirectorySeparator,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$make_directory")))]
    MakeDirectory,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$make_directory_path")))]
    MakeDirectoryPath,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$delete_file")))]
    DeleteFile,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$rename_file")))]
    RenameFile,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$file_copy")))]
    FileCopy,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$working_directory")))]
    WorkingDirectory,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$delete_directory")))]
    DeleteDirectory,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$path_canonical")))]
    PathCanonical,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$file_time")))]
    FileTime,
    #[strum_discriminants(strum(props(Arity = "arity", Name = "$module_call")))]
    DynamicModuleResolution(usize),
    #[strum_discriminants(strum(props(Arity = "arity", Name = "$prepare_call_clause")))]
    PrepareCallClause(usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "$fetch_global_var")))]
    FetchGlobalVar,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$first_stream")))]
    FirstStream,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$flush_output")))]
    FlushOutput,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$get_byte")))]
    GetByte,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$get_char")))]
    GetChar,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$get_n_chars")))]
    GetNChars,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$get_code")))]
    GetCode,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_single_char")))]
    GetSingleChar,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$truncate_if_no_lh_growth_diff")))]
    TruncateIfNoLiftedHeapGrowthDiff,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$truncate_if_no_lh_growth")))]
    TruncateIfNoLiftedHeapGrowth,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$get_attr_list")))]
    GetAttributedVariableList,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_attr_var_queue_delim")))]
    GetAttrVarQueueDelimiter,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$get_attr_var_queue_beyond")))]
    GetAttrVarQueueBeyond,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_b_value")))]
    GetBValue,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$get_cont_chunk")))]
    GetContinuationChunk,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$get_next_op_db_ref")))]
    GetNextOpDBRef,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$lookup_db_ref")))]
    LookupDBRef,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$is_partial_string")))]
    IsPartialString,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$halt")))]
    Halt,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$get_lh_from_offset")))]
    GetLiftedHeapFromOffset,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$get_lh_from_offset_diff")))]
    GetLiftedHeapFromOffsetDiff,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_scc_cleaner")))]
    GetSCCCleaner,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$head_is_dynamic")))]
    HeadIsDynamic,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$install_scc_cleaner")))]
    InstallSCCCleaner,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$install_inference_counter")))]
    InstallInferenceCounter,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$inference_count")))]
    InferenceCount,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$lh_length")))]
    LiftedHeapLength,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$load_library_as_stream")))]
    LoadLibraryAsStream,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$module_exists")))]
    ModuleExists,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$nextEP")))]
    NextEP,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$no_such_predicate")))]
    NoSuchPredicate,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$number_to_chars")))]
    NumberToChars,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$number_to_codes")))]
    NumberToCodes,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$op")))]
    OpDeclaration,
    #[strum_discriminants(strum(props(Arity = "7", Name = "$open")))]
    Open,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$set_stream_options")))]
    SetStreamOptions,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$next_stream")))]
    NextStream,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$partial_string_tail")))]
    PartialStringTail,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$peek_byte")))]
    PeekByte,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$peek_char")))]
    PeekChar,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$peek_code")))]
    PeekCode,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$points_to_cont_reset_marker")))]
    PointsToContinuationResetMarker,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$put_byte")))]
    PutByte,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$put_char")))]
    PutChar,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$put_chars")))]
    PutChars,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$put_code")))]
    PutCode,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$read_query_term")))]
    ReadQueryTerm,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$read_term")))]
    ReadTerm,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$redo_attr_var_binding")))]
    RedoAttrVarBinding,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$remove_call_policy_check")))]
    RemoveCallPolicyCheck,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$remove_inference_counter")))]
    RemoveInferenceCounter,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$reset_cont_marker")))]
    ResetContinuationMarker,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$restore_cut_policy")))]
    RestoreCutPolicy,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_cp")))]
    SetCutPoint(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_input")))]
    SetInput,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_output")))]
    SetOutput,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$store_backtrackable_global_var")))]
    StoreBacktrackableGlobalVar,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$store_global_var")))]
    StoreGlobalVar,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$stream_property")))]
    StreamProperty,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$set_stream_position")))]
    SetStreamPosition,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$inference_level")))]
    InferenceLevel,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$clean_up_block")))]
    CleanUpBlock,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$fail")))]
    Fail,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_ball")))]
    GetBall,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_current_block")))]
    GetCurrentBlock,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_current_scc_block")))]
    GetCurrentSCCBlock,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_cp")))]
    GetCutPoint,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_double_quotes")))]
    GetDoubleQuotes,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$get_unknown")))]
    GetUnknown,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$install_new_block")))]
    InstallNewBlock,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$random_integer")))]
    RandomInteger,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$maybe")))]
    Maybe,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$current_time")))]
    CurrentTime,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$quoted_token")))]
    QuotedToken,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$read_from_chars")))]
    ReadFromChars,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$read_term_from_chars")))]
    ReadTermFromChars,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$reset_block")))]
    ResetBlock,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$reset_scc_block")))]
    ResetSCCBlock,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$return_from_verify_attr")))]
    ReturnFromVerifyAttr,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_ball")))]
    SetBall,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$push_ball_stack")))]
    PushBallStack,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$pop_ball_stack")))]
    PopBallStack,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$pop_from_ball_stack")))]
    PopFromBallStack,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_cp_by_default")))]
    SetCutPointByDefault(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_double_quotes")))]
    SetDoubleQuotes,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_unknown")))]
    SetUnknown,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$set_seed")))]
    SetSeed,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$skip_max_list")))]
    SkipMaxList,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$sleep")))]
    Sleep,
    #[strum_discriminants(strum(props(Arity = "7", Name = "$socket_client_open")))]
    SocketClientOpen,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$socket_server_open")))]
    SocketServerOpen,
    #[strum_discriminants(strum(props(Arity = "7", Name = "$socket_server_accept")))]
    SocketServerAccept,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$socket_server_close")))]
    SocketServerClose,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$tls_accept_client")))]
    TLSAcceptClient,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$tls_client_connect")))]
    TLSClientConnect,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$succeed")))]
    Succeed,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$term_attributed_variables")))]
    TermAttributedVariables,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$term_variables")))]
    TermVariables,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$term_variables_under_max_depth")))]
    TermVariablesUnderMaxDepth,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$truncate_lh_to")))]
    TruncateLiftedHeapTo,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$unify_with_occurs_check")))]
    UnifyWithOccursCheck,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$unwind_environments")))]
    UnwindEnvironments,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$unwind_stack")))]
    UnwindStack,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$wam_instructions")))]
    WAMInstructions,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$inlined_instructions")))]
    InlinedInstructions,
    #[strum_discriminants(strum(props(Arity = "8", Name = "$write_term")))]
    WriteTerm,
    #[strum_discriminants(strum(props(Arity = "8", Name = "$write_term_to_chars")))]
    WriteTermToChars,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$scryer_prolog_version")))]
    ScryerPrologVersion,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$crypto_random_byte")))]
    CryptoRandomByte,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$crypto_data_hash")))]
    CryptoDataHash,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$crypto_hmac")))]
    CryptoHMAC,
    #[strum_discriminants(strum(props(Arity = "7", Name = "$crypto_data_hkdf")))]
    CryptoDataHKDF,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$crypto_password_hash")))]
    CryptoPasswordHash,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$crypto_curve_scalar_mult")))]
    CryptoCurveScalarMult,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$curve25519_scalar_mult")))]
    Curve25519ScalarMult,
    #[cfg(feature = "crypto-full")]
    #[strum_discriminants(strum(props(Arity = "7", Name = "$crypto_data_encrypt")))]
    CryptoDataEncrypt,
    #[cfg(feature = "crypto-full")]
    #[strum_discriminants(strum(props(Arity = "6", Name = "$crypto_data_decrypt")))]
    CryptoDataDecrypt,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$beta")))]
    Beta,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$betai")))]
    BetaI,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$invbetai")))]
    InvBetaI,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$gamma")))]
    Gamma,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$ln_gamma")))]
    LnGamma,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$gammp")))]
    GammP,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$gammq")))]
    GammQ,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$invgammp")))]
    InvGammP,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$erf")))]
    Erf,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$erfc")))]
    Erfc,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$inverf")))]
    InvErf,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$inverfc")))]
    InvErfc,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$ed25519_sign_raw")))]
    Ed25519SignRaw,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$ed25519_verify_raw")))]
    Ed25519VerifyRaw,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$ed25519_seed_to_public_key")))]
    Ed25519SeedToPublicKey,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$first_non_octet")))]
    FirstNonOctet,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$load_html")))]
    LoadHTML,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$load_xml")))]
    LoadXML,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$getenv")))]
    GetEnv,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$setenv")))]
    SetEnv,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$unsetenv")))]
    UnsetEnv,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$shell")))]
    Shell,
    #[strum_discriminants(strum(props(Arity = "8", Name = "$process_create")))]
    ProcessCreate,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$process_id")))]
    ProcessId,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$process_wait")))]
    ProcessWait,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$process_kill")))]
    ProcessKill,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$process_release")))]
    ProcessRelease,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$pid")))]
    Pid,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$chars_base64")))]
    CharsBase64,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$devour_whitespace")))]
    DevourWhitespace,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$is_sto_enabled")))]
    IsSTOEnabled,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$set_sto_as_unify")))]
    SetSTOAsUnify,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$set_nsto_as_unify")))]
    SetNSTOAsUnify,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$set_sto_with_error_as_unify")))]
    SetSTOWithErrorAsUnify,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$home_directory")))]
    HomeDirectory,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$debug_hook")))]
    DebugHook,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$popcount")))]
    PopCount,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$cpu_now")))]
    CpuNow,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$det_length_rundown")))]
    DeterministicLengthRundown,
    #[strum_discriminants(strum(props(Arity = "7", Name = "$http_open")))]
    HttpOpen,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$http_listen")))]
    HttpListen,
    #[strum_discriminants(strum(props(Arity = "7", Name = "$http_accept")))]
    HttpAccept,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$http_answer")))]
    HttpAnswer,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$load_foreign_lib")))]
    LoadForeignLib,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$foreign_call")))]
    ForeignCall,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$define_foreign_struct")))]
    DefineForeignStruct,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$ffi_allocate")))]
    FfiAllocate,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$ffi_read_ptr")))]
    FfiReadPtr,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$ffi_deallocate")))]
    FfiDeallocate,
    #[strum_discriminants(strum(props(Arity = "2", Name = "$js_eval")))]
    JsEval,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$predicate_defined")))]
    PredicateDefined,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$strip_module")))]
    StripModule,
    #[strum_discriminants(strum(props(Arity = "5", Name = "$compile_inline_or_expanded_goal")))]
    CompileInlineOrExpandedGoal,
    #[strum_discriminants(strum(props(Arity = "arity", Name = "$fast_call")))]
    FastCallN(usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "$is_expanded_or_inlined")))]
    IsExpandedOrInlined,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$get_clause_p")))]
    GetClauseP,
    #[strum_discriminants(strum(props(Arity = "6", Name = "$invoke_clause_at_p")))]
    InvokeClauseAtP,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$get_from_attr_list")))]
    GetFromAttributedVarList,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$put_to_attr_list")))]
    PutToAttributedVarList,
    #[strum_discriminants(strum(props(Arity = "3", Name = "$del_from_attr_list")))]
    DeleteFromAttributedVarList,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$delete_all_attributes_from_var")))]
    DeleteAllAttributesFromVar,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$unattributed_var")))]
    UnattributedVar,
    #[strum_discriminants(strum(props(Arity = "4", Name = "$get_db_refs")))]
    GetDBRefs,
    #[strum_discriminants(strum(props(
        Arity = "2",
        Name = "$keysort_with_constant_var_ordering"
    )))]
    KeySortWithConstantVarOrdering,
    #[strum_discriminants(strum(props(Arity = "0", Name = "$inference_limit_exceeded")))]
    InferenceLimitExceeded,
    #[strum_discriminants(strum(props(Arity = "1", Name = "$argv")))]
    Argv,
    Repl(ReplCodePtr),
}

#[allow(dead_code)]
#[derive(ToDeriveInput, EnumDiscriminants)]
#[strum_discriminants(derive(EnumProperty, EnumString))]
enum InstructionTemplate {
    #[strum_discriminants(strum(props(Arity = "3", Name = "get_constant")))]
    GetConstant(Level, HeapCellValue, RegType),
    #[strum_discriminants(strum(props(Arity = "2", Name = "get_list")))]
    GetList(Level, RegType),
    #[strum_discriminants(strum(props(Arity = "4", Name = "get_partial_string")))]
    GetPartialString(Level, Rc<String>, RegType),
    #[strum_discriminants(strum(props(Arity = "3", Name = "get_structure")))]
    GetStructure(Level, Atom, usize, RegType),
    #[strum_discriminants(strum(props(Arity = "2", Name = "get_variable")))]
    GetVariable(RegType, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "get_value")))]
    GetValue(RegType, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "unify_constant")))]
    UnifyConstant(HeapCellValue),
    #[strum_discriminants(strum(props(Arity = "1", Name = "unify_local_value")))]
    UnifyLocalValue(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "unify_variable")))]
    UnifyVariable(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "unify_value")))]
    UnifyValue(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "unify_void")))]
    UnifyVoid(usize),
    // query instruction
    #[strum_discriminants(strum(props(Arity = "3", Name = "put_constant")))]
    PutConstant(Level, HeapCellValue, RegType),
    #[strum_discriminants(strum(props(Arity = "2", Name = "put_list")))]
    PutList(Level, RegType),
    #[strum_discriminants(strum(props(Arity = "4", Name = "put_partial_string")))]
    PutPartialString(Level, Rc<String>, RegType),
    #[strum_discriminants(strum(props(Arity = "3", Name = "put_structure")))]
    PutStructure(Atom, usize, RegType),
    #[strum_discriminants(strum(props(Arity = "2", Name = "put_unsafe_value")))]
    PutUnsafeValue(usize, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "put_value")))]
    PutValue(RegType, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "put_variable")))]
    PutVariable(RegType, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "set_constant")))]
    SetConstant(HeapCellValue),
    #[strum_discriminants(strum(props(Arity = "1", Name = "set_local_value")))]
    SetLocalValue(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "set_variable")))]
    SetVariable(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "set_value")))]
    SetValue(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "set_void")))]
    SetVoid(usize),
    // cut instruction
    #[strum_discriminants(strum(props(Arity = "1", Name = "cut")))]
    Cut(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "cut_prev")))]
    CutPrev(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "get_level")))]
    GetLevel(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "get_prev_level")))]
    GetPrevLevel(RegType),
    #[strum_discriminants(strum(props(Arity = "1", Name = "get_cut_point")))]
    GetCutPoint(RegType),
    #[strum_discriminants(strum(props(Arity = "0", Name = "neck_cut")))]
    NeckCut,
    // choice instruction
    #[strum_discriminants(strum(props(Arity = "3", Name = "dynamic_else")))]
    DynamicElse(usize, Death, NextOrFail),
    #[strum_discriminants(strum(props(Arity = "3", Name = "dynamic_internal_else")))]
    DynamicInternalElse(usize, Death, NextOrFail),
    #[strum_discriminants(strum(props(Arity = "1", Name = "default_retry_me_else")))]
    DefaultRetryMeElse(usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "default_trust_me")))]
    DefaultTrustMe(usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "retry_me_else")))]
    RetryMeElse(usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "trust_me")))]
    TrustMe(usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "default_trust_me")))]
    TryMeElse(usize),
    // arithmetic instruction
    #[strum_discriminants(strum(props(Arity = "2", Name = "add")))]
    Add(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "sub")))]
    Sub(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "mul")))]
    Mul(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "pow")))]
    Pow(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "int_pow")))]
    IntPow(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "i_div")))]
    IDiv(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "max")))]
    Max(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "min")))]
    Min(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "int_floor_div")))]
    IntFloorDiv(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "r_div")))]
    RDiv(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "div")))]
    Div(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "shl")))]
    Shl(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "shr")))]
    Shr(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "xor")))]
    Xor(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "and")))]
    And(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "or")))]
    Or(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "mod")))]
    Mod(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "rem")))]
    Rem(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "2", Name = "gcd")))]
    Gcd(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "sign")))]
    Sign(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "cos")))]
    Cos(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "sin")))]
    Sin(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "tan")))]
    Tan(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "log")))]
    Log(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "exp")))]
    Exp(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "acos")))]
    ACos(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "asin")))]
    ASin(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "atan")))]
    ATan(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "atan2")))]
    ATan2(ArithmeticTerm, ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "sqrt")))]
    Sqrt(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "abs")))]
    Abs(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "float")))]
    Float(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "truncate")))]
    Truncate(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "round")))]
    Round(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "ceiling")))]
    Ceiling(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "floor")))]
    Floor(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "float_fractional_part")))]
    FloatFractionalPart(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "float_integer_part")))]
    FloatIntegerPart(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "neg")))]
    Neg(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "plus")))]
    Plus(ArithmeticTerm, usize),
    #[strum_discriminants(strum(props(Arity = "1", Name = "bitwise_complement")))]
    BitwiseComplement(ArithmeticTerm, usize),
    // control instructions
    #[strum_discriminants(strum(props(Arity = "1", Name = "allocate")))]
    Allocate(usize), // num_frames.
    #[strum_discriminants(strum(props(Arity = "0", Name = "deallocate")))]
    Deallocate,
    #[strum_discriminants(strum(props(Arity = "1", Name = "jmp_by_call")))]
    JmpByCall(usize), // relative offset.
    #[strum_discriminants(strum(props(Arity = "1", Name = "rev_jmp_by")))]
    RevJmpBy(usize),
    #[strum_discriminants(strum(props(Arity = "0", Name = "proceed")))]
    Proceed,
    // indexing.
    #[strum_discriminants(strum(props(Arity = "1", Name = "indexing_code")))]
    IndexingCode(Vec<IndexingLine>),
    // break from loop instruction.
    #[strum_discriminants(strum(props(Arity = "0", Name = "break_from_dispatch")))]
    BreakFromDispatchLoop,
    // run verify_attr, eventually.
    #[strum_discriminants(strum(props(Arity = "0", Name = "run_verify_attr")))]
    RunVerifyAttr,
    // procedures
    CallClause(ClauseType, usize, usize, bool, bool), // ClauseType,
                                                      // arity,
                                                      // perm_vars,
                                                      // last_call,
                                                      // use_default_call_policy.
}

fn derive_input(ty: &Type) -> Option<DeriveInput> {
    let clause_type: Type = parse_quote! { ClauseType };
    let built_in_clause_type: Type = parse_quote! { BuiltInClauseType };
    let inlined_clause_type: Type = parse_quote! { InlinedClauseType };
    let system_clause_type: Type = parse_quote! { SystemClauseType };
    let compare_term_type: Type = parse_quote! { CompareTerm };
    let compare_number_type: Type = parse_quote! { CompareNumber };
    let repl_code_ptr_type: Type = parse_quote! { ReplCodePtr };

    if ty == &clause_type {
        Some(ClauseType::to_derive_input())
    } else if ty == &built_in_clause_type {
        Some(BuiltInClauseType::to_derive_input())
    } else if ty == &inlined_clause_type {
        Some(InlinedClauseType::to_derive_input())
    } else if ty == &system_clause_type {
        Some(SystemClauseType::to_derive_input())
    } else if ty == &compare_number_type {
        Some(CompareNumber::to_derive_input())
    } else if ty == &compare_term_type {
        Some(CompareTerm::to_derive_input())
    } else if ty == &repl_code_ptr_type {
        Some(ReplCodePtr::to_derive_input())
    } else {
        None
    }
}

impl ToTokens for Arity {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Arity::Static(arity) => {
                arity.to_tokens(tokens);
            }
            Arity::Ident(arity) => {
                let ident = format_ident!("{}", arity);
                tokens.append(ident);
            }
        }
    }
}

fn add_discriminant_data<DiscriminantT>(
    variant: &Variant,
    prefix: &'static str,
    variant_data: &mut Vec<(&'static str, Arity, Variant)>,
) -> (&'static str, Arity)
where
    DiscriminantT: FromStr + strum::EnumProperty + std::fmt::Debug,
{
    let name = prop_from_ident::<DiscriminantT>(&variant.ident, "Name");
    let arity = Arity::from(prop_from_ident::<DiscriminantT>(&variant.ident, "Arity"));

    if prefix == "Call" {
        let mut variant = variant.clone();
        variant.attrs.clear();

        variant_data.push((name, arity, variant));
    }

    (name, arity)
}

pub fn generate_instructions_rs() -> TokenStream {
    let input = InstructionTemplate::to_derive_input();
    let mut instr_data = InstructionData::new();

    instr_data.generate_instruction_enum_loop(input);

    let instr_variants: Vec<_> = instr_data
        .instr_variants
        .iter()
        .cloned()
        .map(|(_, _, _, variant)| variant)
        .collect();

    fn attributeless_enum<T: ToDeriveInput>() -> Vec<Variant> {
        if let Data::Enum(DataEnum { mut variants, .. }) = T::to_derive_input().data {
            for variant in &mut variants {
                variant.attrs.clear();
            }

            variants.into_iter().collect()
        } else {
            unreachable!()
        }
    }

    let clause_type_variants = attributeless_enum::<ClauseType>();
    let builtin_type_variants = attributeless_enum::<BuiltInClauseType>();
    let inlined_type_variants = attributeless_enum::<InlinedClauseType>();
    let system_clause_type_variants = attributeless_enum::<SystemClauseType>();
    let repl_code_ptr_variants = attributeless_enum::<ReplCodePtr>();
    let compare_number_variants = attributeless_enum::<CompareNumber>();
    let compare_term_variants = attributeless_enum::<CompareTerm>();

    let mut clause_type_from_name_and_arity_arms = vec![];
    let mut clause_type_to_instr_arms = vec![];
    let mut clause_type_name_arms = vec![];
    let mut is_inbuilt_arms = vec![];
    let mut is_inlined_arms = vec![];

    is_inbuilt_arms.push(quote! {
        (atom!(":-"), 1 | 2)
    });

    for (name, arity, variant) in instr_data.compare_number_variants {
        let ident = variant.ident.clone();

        let variant_fields: Vec<_> = variant
            .fields
            .into_iter()
            .map(|field| {
                let ty = field.ty;
                quote! { #ty::default() }
            })
            .collect();

        clause_type_from_name_and_arity_arms.push(if !variant_fields.is_empty() {
            quote! {
                (atom!(#name), #arity) => ClauseType::Inlined(
                    InlinedClauseType::CompareNumber(CompareNumber::#ident(#(#variant_fields),*))
                )
            }
        } else {
            quote! {
                (atom!(#name), #arity) => ClauseType::Inlined(
                    InlinedClauseType::CompareNumber(CompareNumber::#ident)
                )
            }
        });

        clause_type_name_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::Inlined(
                    InlinedClauseType::CompareNumber(CompareNumber::#ident(..))
                ) => atom!(#name)
            }
        } else {
            quote! {
                ClauseType::Inlined(
                    InlinedClauseType::CompareNumber(CompareNumber::#ident)
                ) => (atom!(#name), #arity)
            }
        });

        let ident = variant.ident;
        let instr_ident = format_ident!("Call{}", ident);

        let placeholder_ids: Vec<_> = (0..variant_fields.len())
            .map(|n| format_ident!("f_{}", n))
            .collect();

        clause_type_to_instr_arms.push(quote! {
            ClauseType::Inlined(
                InlinedClauseType::CompareNumber(CompareNumber::#ident(#(#placeholder_ids),*))
            ) => Instruction::#instr_ident(#(*#placeholder_ids),*)
        });

        is_inbuilt_arms.push(quote! {
            (atom!(#name), #arity)
        });

        is_inlined_arms.push(quote! {
            (atom!(#name), #arity)
        });
    }

    for (name, arity, variant) in instr_data.compare_term_variants {
        let ident = variant.ident.clone();

        clause_type_from_name_and_arity_arms.push(quote! {
            (atom!(#name), #arity) => ClauseType::BuiltIn(
                BuiltInClauseType::CompareTerm(CompareTerm::#ident)
            )
        });

        clause_type_name_arms.push(quote! {
            ClauseType::BuiltIn(
                BuiltInClauseType::CompareTerm(CompareTerm::#ident)
            ) => atom!(#name)
        });

        let ident = variant.ident;
        let instr_ident = format_ident!("Call{}", ident);

        clause_type_to_instr_arms.push(quote! {
            ClauseType::BuiltIn(
                BuiltInClauseType::CompareTerm(CompareTerm::#ident)
            ) => Instruction::#instr_ident
        });

        is_inbuilt_arms.push(quote! {
            (atom!(#name), #arity)
        });
    }

    for (name, arity, variant) in instr_data.builtin_type_variants {
        let ident = variant.ident.clone();

        let variant_fields: Vec<_> = variant
            .fields
            .into_iter()
            .map(|field| {
                let ty = field.ty;
                quote! { #ty::default() }
            })
            .collect();

        clause_type_from_name_and_arity_arms.push(if !variant_fields.is_empty() {
            quote! {
                (atom!(#name), #arity) => ClauseType::BuiltIn(
                    BuiltInClauseType::#ident(#(#variant_fields),*)
                )
            }
        } else {
            quote! {
                (atom!(#name), #arity) => ClauseType::BuiltIn(
                    BuiltInClauseType::#ident
                )
            }
        });

        clause_type_name_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::BuiltIn(
                    BuiltInClauseType::#ident(..)
                ) => atom!(#name)
            }
        } else {
            quote! {
                ClauseType::BuiltIn(
                    BuiltInClauseType::#ident
                ) => atom!(#name)
            }
        });

        let ident = variant.ident;
        let instr_ident = format_ident!("Call{}", ident);

        let placeholder_ids: Vec<_> = (0..variant_fields.len())
            .map(|n| format_ident!("f_{}", n))
            .collect();

        clause_type_to_instr_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::BuiltIn(
                    BuiltInClauseType::#ident(#(#placeholder_ids),*)
                ) => Instruction::#instr_ident(#(*#placeholder_ids),*)
            }
        } else {
            quote! {
                ClauseType::BuiltIn(
                    BuiltInClauseType::#ident
                ) => Instruction::#instr_ident
            }
        });

        is_inbuilt_arms.push(quote! {
            (atom!(#name), #arity)
        });
    }

    for (name, arity, variant) in instr_data.inlined_type_variants {
        let ident = variant.ident.clone();

        let variant_fields: Vec<_> = variant
            .fields
            .into_iter()
            .map(|field| {
                if field.ty.type_id() == TypeId::of::<usize>() {
                    quote! { #arity }
                } else {
                    let ty = field.ty;
                    quote! { #ty::default() }
                }
            })
            .collect();

        clause_type_from_name_and_arity_arms.push(if !variant_fields.is_empty() {
            quote! {
                (atom!(#name), #arity) => ClauseType::Inlined(
                    InlinedClauseType::#ident(#(#variant_fields),*)
                )
            }
        } else {
            quote! {
                (atom!(#name), #arity) => ClauseType::Inlined(
                    InlinedClauseType::#ident
                )
            }
        });

        clause_type_name_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::Inlined(
                    InlinedClauseType::#ident(..)
                ) => atom!(#name)
            }
        } else {
            quote! {
                ClauseType::Inlined(
                    InlinedClauseType::#ident
                ) => atom!(#name)
            }
        });

        let ident = variant.ident;
        let instr_ident = format_ident!("Call{}", ident);

        let placeholder_ids: Vec<_> = (0..variant_fields.len())
            .map(|n| format_ident!("f_{}", n))
            .collect();

        clause_type_to_instr_arms.push(quote! {
            ClauseType::Inlined(
                InlinedClauseType::#ident(#(#placeholder_ids),*)
            ) => Instruction::#instr_ident(*#(#placeholder_ids),*)
        });

        is_inbuilt_arms.push(quote! {
            (atom!(#name), #arity)
        });

        is_inlined_arms.push(quote! {
            (atom!(#name), #arity)
        });
    }

    for (name, arity, variant) in instr_data.system_clause_type_variants {
        let ident = variant.ident.clone();
        let ident_s = ident.to_string();

        let variant_fields: Vec<_> = variant
            .fields
            .into_iter()
            .map(|field| {
                if field.ty == parse_quote! { usize } {
                    quote! { #arity }
                } else {
                    let ty = field.ty;
                    quote! { #ty::default() }
                }
            })
            .collect();

        clause_type_from_name_and_arity_arms.push(if !variant_fields.is_empty() {
            if ident_s == "SetCutPoint" || ident_s == "SetCutPointByDefault" {
                quote! {
                    (atom!(#name), #arity) => ClauseType::System(
                        SystemClauseType::#ident(temp_v!(1))
                    )
                }
            } else if ident_s == "InlineCallN" {
                quote! {
                    (atom!(#name), arity) => ClauseType::System(
                        SystemClauseType::#ident(arity)
                    )
                }
            } else {
                quote! {
                    (atom!(#name), #arity) => ClauseType::System(
                        SystemClauseType::#ident(#(#variant_fields),*)
                    )
                }
            }
        } else {
            quote! {
                (atom!(#name), #arity) => ClauseType::System(
                    SystemClauseType::#ident
                )
            }
        });

        clause_type_name_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::System(
                    SystemClauseType::#ident(..)
                ) => atom!(#name)
            }
        } else {
            quote! {
                ClauseType::System(
                    SystemClauseType::#ident
                ) => atom!(#name)
            }
        });

        let ident = variant.ident;

        let instr_ident = if ident != "CallContinuation" {
            format_ident!("Call{}", ident)
        } else {
            ident.clone()
        };

        let placeholder_ids: Vec<_> = (0..variant_fields.len())
            .map(|n| format_ident!("f_{}", n))
            .collect();

        clause_type_to_instr_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::System(
                    SystemClauseType::#ident(#(#placeholder_ids),*)
                ) => Instruction::#instr_ident(#(*#placeholder_ids),*)
            }
        } else {
            quote! {
                ClauseType::System(
                    SystemClauseType::#ident
                ) => Instruction::#instr_ident
            }
        });

        is_inbuilt_arms.push(if let Arity::Ident("arity") = &arity {
            quote! {
                (atom!(#name), _)
            }
        } else {
            quote! {
                (atom!(#name), #arity)
            }
        });
    }

    for (name, arity, variant) in instr_data.repl_code_ptr_variants {
        let ident = variant.ident.clone();

        let variant_fields: Vec<_> = variant
            .fields
            .into_iter()
            .map(|field| {
                if field.ty.type_id() == TypeId::of::<usize>() {
                    quote! { #arity }
                } else {
                    let ty = field.ty;
                    quote! { #ty::default() }
                }
            })
            .collect();

        clause_type_from_name_and_arity_arms.push(if !variant_fields.is_empty() {
            quote! {
                (atom!(#name), #arity) => ClauseType::System(SystemClauseType::Repl(
                    ReplCodePtr::#ident(#(#variant_fields),*)
                ))
            }
        } else {
            quote! {
                (atom!(#name), #arity) => ClauseType::System(SystemClauseType::Repl(
                    ReplCodePtr::#ident
                ))
            }
        });

        clause_type_name_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::System(
                    SystemClauseType::Repl(ReplCodePtr::#ident(..))
                ) => atom!(#name)
            }
        } else {
            quote! {
                ClauseType::System(
                    SystemClauseType::Repl(ReplCodePtr::#ident)
                ) => atom!(#name)
            }
        });

        let ident = variant.ident;
        let instr_ident = format_ident!("Call{}", ident);

        let placeholder_ids: Vec<_> = (0..variant_fields.len())
            .map(|n| format_ident!("f_{}", n))
            .collect();

        clause_type_to_instr_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::System(SystemClauseType::Repl(
                    ReplCodePtr::#ident(#(#placeholder_ids),*)
                )) => Instruction::#instr_ident(#(*#placeholder_ids),*)
            }
        } else {
            quote! {
                ClauseType::System(SystemClauseType::Repl(
                    ReplCodePtr::#ident
                )) => Instruction::#instr_ident
            }
        });

        is_inbuilt_arms.push(quote! {
            (atom!(#name), #arity)
        });
    }

    for (name, arity, variant) in instr_data.clause_type_variants {
        let ident = variant.ident.clone();

        if ident == "Named" {
            clause_type_from_name_and_arity_arms.push(quote! {
                (name, arity) => ClauseType::Named(arity, name, CodeIndex::default(&mut arena.code_index_tbl))
            });

            clause_type_to_instr_arms.push(quote! {
                ClauseType::Named(arity, name, idx) => Instruction::CallNamed(*arity, *name, *idx)
            });

            clause_type_name_arms.push(quote! {
                ClauseType::Named(_, name, _) => *name
            });

            continue;
        }

        let variant_fields: Vec<_> = variant
            .fields
            .into_iter()
            .map(|field| {
                if field.ty == parse_quote! { usize } {
                    quote! { #arity }
                } else {
                    let ty = field.ty;
                    quote! { #ty::default() }
                }
            })
            .collect();

        clause_type_from_name_and_arity_arms.push(if !variant_fields.is_empty() {
            quote! {
                (atom!(#name), #arity) => ClauseType::#ident(#(#variant_fields),*)
            }
        } else {
            quote! {
                (atom!(#name), #arity) => ClauseType::#ident
            }
        });

        clause_type_name_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::#ident(..) => atom!(#name)
            }
        } else {
            quote! {
                ClauseType::#ident => atom!(#name)
            }
        });

        let ident = variant.ident;

        let placeholder_ids: Vec<_> = (0..variant_fields.len())
            .map(|n| format_ident!("f_{}", n))
            .collect();

        clause_type_to_instr_arms.push(if !variant_fields.is_empty() {
            quote! {
                ClauseType::#ident(#(#placeholder_ids),*) =>
                    Instruction::#ident(#(*#placeholder_ids),*)
            }
        } else {
            quote! {
                ClauseType::#ident => Instruction::#ident
            }
        });

        is_inbuilt_arms.push(quote! {
            (atom!(#name), _)
        });
    }

    let to_execute_arms: Vec<_> = instr_data
        .instr_variants
        .iter()
        .cloned()
        .filter_map(|(_, _, _, variant)| {
            let variant_ident = variant.ident.clone();
            let variant_string = variant.ident.to_string();

            let enum_arity = if let Fields::Unnamed(fields) = &variant.fields {
                fields.unnamed.len()
            } else {
                0
            };

            let placeholder_ids: Vec<_> =
                (0..enum_arity).map(|n| format_ident!("f_{}", n)).collect();

            if let Some(variant_suffix) = variant_string.strip_prefix("Call") {
                let execute_ident = format_ident!("Execute{}", variant_suffix);

                Some(if enum_arity == 0 {
                    quote! {
                        Instruction::#variant_ident =>
                            Instruction::#execute_ident
                    }
                } else {
                    quote! {
                        Instruction::#variant_ident(#(#placeholder_ids),*) =>
                            Instruction::#execute_ident(#(#placeholder_ids),*)
                    }
                })
            } else if let Some(variant_suffix) = variant_string.strip_prefix("DefaultCall") {
                let execute_ident = format_ident!("DefaultExecute{}", variant_suffix);

                Some(if enum_arity == 0 {
                    quote! {
                        Instruction::#variant_ident =>
                            Instruction::#execute_ident
                    }
                } else {
                    quote! {
                        Instruction::#variant_ident(#(#placeholder_ids),*) =>
                            Instruction::#execute_ident(#(#placeholder_ids),*)
                    }
                })
            } else {
                None
            }
        })
        .collect();

    let is_execute_arms: Vec<_> = instr_data
        .instr_variants
        .iter()
        .cloned()
        .filter_map(|(_, _, _, variant)| {
            let variant_ident = variant.ident.clone();
            let variant_string = variant.ident.to_string();

            let enum_arity = if let Fields::Unnamed(fields) = &variant.fields {
                fields.unnamed.len()
            } else {
                0
            };

            if variant_string.starts_with("Execute") || variant_string.starts_with("DefaultExecute")
            {
                Some(if enum_arity == 0 {
                    quote! {
                        Instruction::#variant_ident
                    }
                } else {
                    quote! {
                        Instruction::#variant_ident(..)
                    }
                })
            } else if variant_string == "JmpByExecute" {
                Some(quote! {
                    Instruction::#variant_ident(..)
                })
            } else {
                None
            }
        })
        .collect();

    let to_default_arms: Vec<_> = instr_data
        .instr_variants
        .iter()
        .cloned()
        .filter_map(|(_, _, countable_inference, variant)| {
            if !is_non_default_callable(&variant.ident) {
                return None;
            }

            if let CountableInference::HasDefault = countable_inference {
                let variant_ident = variant.ident.clone();
                let def_variant_ident = format_ident!("Default{}", variant.ident);
                let enum_arity = if let Fields::Unnamed(fields) = &variant.fields {
                    fields.unnamed.len()
                } else {
                    0
                };

                let placeholder_ids: Vec<_> =
                    (0..enum_arity).map(|n| format_ident!("f_{}", n)).collect();

                Some(if enum_arity == 0 {
                    quote! {
                        Instruction::#variant_ident =>
                            Instruction::#def_variant_ident
                    }
                } else {
                    quote! {
                        Instruction::#variant_ident(#(#placeholder_ids),*) =>
                            Instruction::#def_variant_ident(#(#placeholder_ids),*)
                    }
                })
            } else {
                None
            }
        })
        .collect();

    let control_flow_arms: Vec<_> = instr_data
        .instr_variants
        .iter()
        .cloned()
        .filter_map(|(_, _, _, variant)| {
            if !is_callable(&variant.ident) && !is_jmp(&variant.ident) {
                return None;
            }

            let enum_arity = if let Fields::Unnamed(fields) = &variant.fields {
                fields.unnamed.len()
            } else {
                0
            };

            let variant_ident = variant.ident.clone();

            Some(if enum_arity == 0 {
                quote! {
                    Instruction::#variant_ident
                }
            } else {
                quote! {
                    Instruction::#variant_ident(..)
                }
            })
        })
        .collect();

    let instr_macro_arms: Vec<_> = instr_data
        .instr_variants
        .iter()
        .rev() // produce default, execute & default & execute cases first.
        .map(|(name, arity, _, variant)| {
            let variant_ident = variant.ident.clone();
            let variant_string = variant.ident.to_string();
            let arity = match *arity {
                Arity::Static(arity) => arity,
                _ => 1,
            };

            #[allow(clippy::collapsible_else_if)]
            Some(if variant_string.starts_with("Execute") {
                if arity == 0 {
                    quote! {
                        (#name, execute) => {
                            Instruction::#variant_ident
                        }
                    }
                } else {
                    quote! {
                        (#name, execute, $($args:expr),*) => {
                            Instruction::#variant_ident($($args),*)
                        }
                    }
                }
            } else if variant_string.starts_with("Call") {
                if arity == 0 {
                    quote! {
                        (#name) => {
                            Instruction::#variant_ident
                        }
                    }
                } else {
                    quote! {
                        (#name, $($args:expr),*) => {
                            Instruction::#variant_ident($($args),*)
                        }
                    }
                }
            } else if variant_string.starts_with("DefaultExecute") {
                if arity == 0 {
                    quote! {
                        (#name, execute, default) => {
                            Instruction::#variant_ident
                        }
                    }
                } else {
                    quote! {
                        (#name, execute, default, $($args:expr),*) => {
                            Instruction::#variant_ident($($args),*)
                        }
                    }
                }
            } else if variant_string.starts_with("DefaultCall") {
                if arity == 0 {
                    quote! {
                        (#name, default) => {
                            Instruction::#variant_ident
                        }
                    }
                } else {
                    quote! {
                        (#name, default, $($args:expr),*) => {
                            Instruction::#variant_ident($($args),*)
                        }
                    }
                }
            } else {
                if arity == 0 {
                    quote! {
                        (#name) => {
                            Instruction::#variant_ident
                        }
                    }
                } else {
                    quote! {
                        (#name, $($args:expr),*) => {
                            Instruction::#variant_ident($($args),*)
                        }
                    }
                }
            })
        })
        .collect();

    let name_and_arity_arms: Vec<_> = instr_data
        .instr_variants
        .into_iter()
        .map(|(name, arity, _, variant)| {
            let ident = &variant.ident;

            let enum_arity = if let Fields::Unnamed(fields) = &variant.fields {
                fields.unnamed.len()
            } else {
                0
            };

            match arity {
                Arity::Static(_) if enum_arity == 0 => {
                    quote! { Instruction::#ident => (atom!(#name), #arity) }
                }
                Arity::Static(_) => {
                    quote! { Instruction::#ident(..) => (atom!(#name), #arity) }
                }
                Arity::Ident(_) if enum_arity == 0 => {
                    quote! { &Instruction::#ident(#arity) => (atom!(#name), #arity) }
                }
                Arity::Ident(_) => {
                    quote! { &Instruction::#ident(#arity, ..) => (atom!(#name), #arity) }
                }
            }
        })
        .collect();

    quote! {
        #[allow(clippy::enum_variant_names)]
        #[derive(Clone, Debug)]
        pub enum CompareTerm {
            #(
                #compare_term_variants,
            )*
        }

        #[allow(clippy::enum_variant_names)]
        #[derive(Clone, Copy, Debug)]
        pub enum CompareNumber {
            #(
                #compare_number_variants,
            )*
        }


        #[derive(Clone, Debug)]
        pub enum BuiltInClauseType {
            #(
                #builtin_type_variants,
            )*
        }

        #[derive(Clone, Debug)]
        pub enum InlinedClauseType {
            #(
                #inlined_type_variants,
            )*
        }

        #[derive(Clone, Debug)]
        pub enum SystemClauseType {
            #(
                #system_clause_type_variants,
            )*
        }

        #[derive(Clone, Debug)]
        pub enum ReplCodePtr {
            #(
                #repl_code_ptr_variants,
            )*
        }

        #[derive(Clone, Debug)]
        pub enum ClauseType {
            #(
                #clause_type_variants,
            )*
        }

        impl ClauseType {
            pub fn from(name: Atom, arity: usize, arena: &mut Arena) -> ClauseType {
                match (name, arity) {
                    #(
                        #clause_type_from_name_and_arity_arms,
                    )*
                }
            }

            pub fn to_instr(&self) -> Instruction {
                match self {
                    #(
                        #clause_type_to_instr_arms,
                    )*
                }
            }

            pub fn name(&self) -> Atom {
                match self {
                    #(
                        #clause_type_name_arms,
                    )*
                }
            }

            pub fn is_inbuilt(name: Atom, arity: usize) -> bool {
                matches!((name, arity),
                    #(#is_inbuilt_arms)|*
                )
            }

            pub fn is_inlined(name: Atom, arity: usize) -> bool {
                matches!((name, arity),
                    #(#is_inlined_arms)|*
                )
            }
        }

        #[derive(Clone, Debug)]
        pub enum Instruction {
            #(
                #instr_variants,
            )*
        }

        impl Instruction {
            pub fn to_name_and_arity(&self) -> (Atom, usize) {
                match self {
                    #(
                        #name_and_arity_arms,
                    )*
                }
            }

            pub fn into_default(self) -> Instruction {
                match self {
                    #(
                        #to_default_arms,
                    )*
                    _ => self,
                }
            }

            pub fn into_execute(self) -> Instruction {
                match self {
                    #(
                        #to_execute_arms,
                    )*
                    _ => self
                }
            }

            pub fn is_execute(&self) -> bool {
                matches!(self,
                    #(#is_execute_arms)|*
                )
            }

            #[allow(dead_code)]
            pub fn is_ctrl_instr(&self) -> bool {
                matches!(self,
                    Instruction::Allocate(_) |
                    Instruction::Deallocate |
                    Instruction::Proceed |
                    Instruction::RevJmpBy(_) |
                    #(#control_flow_arms)|*
                )
            }

        }

        macro_rules! _instr {
            #(
                #instr_macro_arms
            );*
        }

        // https://github.com/rust-lang/rust/pull/52234#issuecomment-976702997
        pub(crate) use _instr as instr;
    }
}

fn is_callable(id: &Ident) -> bool {
    let id = id.to_string();

    id.starts_with("Call")
        || id.starts_with("Execute")
        || id.starts_with("DefaultCall")
        || id.starts_with("DefaultExecute")
}

fn is_non_default_callable(id: &Ident) -> bool {
    let id = id.to_string();
    id.starts_with("Call") || id.starts_with("Execute")
}

fn is_jmp(id: &Ident) -> bool {
    let id = id.to_string();
    id.starts_with("JmpByCall") || id.starts_with("JmpByExecute")
}

fn create_instr_variant(id: Ident, mut variant: Variant) -> Variant {
    variant.ident = id;
    variant.attrs.clear();

    variant
}

fn prop_from_ident<DiscriminantT>(id: &Ident, key: &'static str) -> &'static str
where
    DiscriminantT: FromStr + strum::EnumProperty + std::fmt::Debug,
{
    let disc = match DiscriminantT::from_str(id.to_string().as_str()) {
        Ok(disc) => disc,
        Err(_) => {
            panic!("can't generate discriminant {id}");
        }
    };

    match disc.get_str(key) {
        Some(prop) => prop,
        None => {
            panic!("can't find property {key} of discriminant {disc:?}");
        }
    }
}

#[derive(Clone, Copy)]
enum Arity {
    Static(usize),
    Ident(&'static str),
}

impl From<&'static str> for Arity {
    fn from(arity: &'static str) -> Self {
        arity
            .parse::<usize>()
            .map(Arity::Static)
            .unwrap_or_else(|_| Arity::Ident(arity))
    }
}

#[derive(Clone, Copy)]
enum CountableInference {
    HasDefault,
    NotCounted,
}

struct InstructionData {
    instr_variants: Vec<(&'static str, Arity, CountableInference, Variant)>,
    clause_type_variants: Vec<(&'static str, Arity, Variant)>,
    builtin_type_variants: Vec<(&'static str, Arity, Variant)>,
    inlined_type_variants: Vec<(&'static str, Arity, Variant)>,
    system_clause_type_variants: Vec<(&'static str, Arity, Variant)>,
    compare_number_variants: Vec<(&'static str, Arity, Variant)>,
    compare_term_variants: Vec<(&'static str, Arity, Variant)>,
    repl_code_ptr_variants: Vec<(&'static str, Arity, Variant)>,
}

impl InstructionData {
    fn new() -> Self {
        Self {
            instr_variants: vec![],
            clause_type_variants: vec![],
            builtin_type_variants: vec![],
            inlined_type_variants: vec![],
            system_clause_type_variants: vec![],
            compare_number_variants: vec![],
            compare_term_variants: vec![],
            repl_code_ptr_variants: vec![],
        }
    }

    fn label_variant(&mut self, id: &Ident, prefix: &'static str, variant: Variant) {
        let (name, arity, countable_inference) = if id == "CompareNumber" {
            let (name, arity) = add_discriminant_data::<CompareNumberDiscriminants>(
                &variant,
                prefix,
                &mut self.compare_number_variants,
            );

            (name, arity, CountableInference::HasDefault)
        } else if id == "CompareTerm" {
            let (name, arity) = add_discriminant_data::<CompareTermDiscriminants>(
                &variant,
                prefix,
                &mut self.compare_term_variants,
            );

            (name, arity, CountableInference::HasDefault)
        } else if id == "BuiltInClauseType" {
            let (name, arity) = add_discriminant_data::<BuiltInClauseTypeDiscriminants>(
                &variant,
                prefix,
                &mut self.builtin_type_variants,
            );

            (name, arity, CountableInference::HasDefault)
        } else if id == "InlinedClauseType" {
            let (name, arity) = add_discriminant_data::<InlinedClauseTypeDiscriminants>(
                &variant,
                prefix,
                &mut self.inlined_type_variants,
            );

            (name, arity, CountableInference::NotCounted)
        } else if id == "ReplCodePtr" {
            let (name, arity) = add_discriminant_data::<ReplCodePtrDiscriminants>(
                &variant,
                prefix,
                &mut self.repl_code_ptr_variants,
            );

            (name, arity, CountableInference::NotCounted)
        } else if id == "SystemClauseType" {
            let (name, arity) = add_discriminant_data::<SystemClauseTypeDiscriminants>(
                &variant,
                prefix,
                &mut self.system_clause_type_variants,
            );

            (name, arity, CountableInference::NotCounted)
        } else if id == "InstructionTemplate" {
            (
                prop_from_ident::<InstructionTemplateDiscriminants>(&variant.ident, "Name"),
                Arity::from(prop_from_ident::<InstructionTemplateDiscriminants>(
                    &variant.ident,
                    "Arity",
                )),
                CountableInference::NotCounted,
            )
        } else if id == "ClauseType" {
            let (name, arity) = add_discriminant_data::<ClauseTypeDiscriminants>(
                &variant,
                prefix,
                &mut self.clause_type_variants,
            );

            (name, arity, CountableInference::HasDefault)
        } else {
            panic!("type ID is: {id}");
        };

        let v_ident = variant
            .ident
            .to_string()
            .strip_prefix("Call")
            .map(|s| format_ident!("{}", s))
            .unwrap_or_else(|| variant.ident.clone());

        let generated_variant =
            create_instr_variant(format_ident!("{}{}", prefix, v_ident), variant.clone());

        self.instr_variants
            .push((name, arity, countable_inference, generated_variant));
    }

    fn generate_instruction_enum_loop(&mut self, input: syn::DeriveInput) {
        if let Data::Enum(DataEnum { variants, .. }) = input.data {
            for mut variant in variants {
                if let Some(field) = variant.fields.iter().next() {
                    if let Some(input) = derive_input(&field.ty) {
                        self.generate_instruction_enum_loop(input);
                        continue;
                    }
                }

                if input.ident == "InstructionTemplate" {
                    variant.attrs.clear();
                    self.label_variant(&input.ident, "", variant);
                    continue;
                }

                self.label_variant(&input.ident, "Call", variant.clone());
                self.label_variant(&input.ident, "Execute", variant.clone());

                if input.ident == "BuiltInClauseType"
                    || input.ident == "CompareNumber"
                    || input.ident == "CompareTerm"
                    || input.ident == "ClauseType"
                {
                    self.label_variant(&input.ident, "DefaultCall", variant.clone());
                    self.label_variant(&input.ident, "DefaultExecute", variant);
                }
            }
        } else {
            panic!("{} must be an enum!", input.ident);
        }
    }
}
