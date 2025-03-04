//! Scan all of a function's BBs and determine the read/write deps for each.

use std::collections::HashMap;

use cranelift_codegen::ir::{AbiParam, Function, Signature, UserExternalName, UserFuncName};
use cranelift_codegen::isa::CallConv;
use rustc_abi::ExternAbi;
use rustc_codegen_ssa::common::TypeKind;
use rustc_hir::Safety;
use rustc_middle::mir::{BasicBlock, Body, Local, Statement};
use rustc_middle::ty::layout::FnAbiOf;
use rustc_middle::ty::{self, PseudoCanonicalInput, Ty, TyCtxt, TyKind};
use rustc_mir_dataflow::impls::MaybeLiveLocals;
use rustc_mir_dataflow::{Analysis, ResultsCursor};
use rustc_target::callconv::FnAbi;

use crate::{FullyMonomorphizedLayoutCx, FunctionCx, clif_type_from_ty};

/// When we generate a function from a BB, if we ever want to add additional "statements", we need to do this after the rest of the clif has been generated.
///
/// This enum is storing info in order to generate it later.
enum AdditionalTermInfo {
    Call,

    /// From branch.
    MultiCall,
    Return,
}

pub(crate) struct GeneratedFuncInfo<'a> {
    pub(crate) func: Function,
    pub(crate) bb_args_and_return: BasicBlockArgsAndReturn<'a>,
    pub(crate) additional_term_info: AdditionalTermInfo,
    pub(crate) local_replace_map: LocalReplaceMap,
    pub(crate) func_name: String,
}

impl<'a> BasicBlockArgsAndReturn<'a> {
    pub(crate) fn create_fn_abi<'b>(&'b self, tcx: TyCtxt<'a>) -> &'b FnAbi<'a, Ty<'a>> {
        let inputs = self.args.iter().map(|arg_info| arg_info.param_type);

        let ret_tuple = tcx.mk_type_list(
            &self.return_info.iter().map(|ret_info| ret_info.param_type).collect::<Vec<_>>(),
        );
        let output_tup = match self.return_info.is_empty() {
            false => tcx.mk_ty_from_kind(TyKind::Tuple(ret_tuple)),
            true => tcx.types.unit,
        };

        let sig = tcx.mk_fn_sig(inputs, output_tup, false, Safety::Safe, ExternAbi::Rust);
        let fn_ptr_ty = ty::Binder::dummy(sig);

        FullyMonomorphizedLayoutCx(tcx).fn_abi_of_fn_ptr(fn_ptr_ty, ty::List::empty())
    }
}

struct ProcessedBB<'a> {
    bb_key: BasicBlock,
    arg_and_ret_info: BasicBlockArgsAndReturn<'a>,
    term_info: AdditionalTermInfo,
}

struct BasicBlockArgsAndReturn<'a> {
    args: Vec<BasicBlockFuncArg<'a>>,
    return_info: Vec<BasicBlockRetParam<'a>>,
}

struct LocalReplaceMap {
    pub(crate) map: HashMap<Local, Local>,
}

impl LocalReplaceMap {
    fn new(arg_and_ret_info: &BasicBlockArgsAndReturn<'_>) -> Self {
        // `0` is always reserved for the return type.
        // We're going to map the first set of locals to the args and then reserve the following after that for the return params.

        let mut next_local_ident = 1;
        let mut map = HashMap::new();

        for arg_info in arg_and_ret_info.args.iter() {
            map.insert(arg_info.orig_local, Local::from_usize(next_local_ident));
            next_local_ident += 1;
        }

        for ret_info in arg_and_ret_info.return_info.iter() {
            map.insert(ret_info.orig_local, Local::from_usize(next_local_ident));
            next_local_ident += 1;
        }

        Self { map }
    }

    fn rewrite_locals_in_bb_statements(&mut self, orig_statements: &mut Vec<Statement<'_>>) {
        let mut next_local_ident = self.map.len() + 1;

        for s in orig_statements.iter_mut() {
            let statement_locals = extract_locals_from_statement(s);
            for statement_local in statement_locals {
                let local_remap = self.map.entry(*statement_local).or_insert_with(|| {
                    let new_local = Local::from_usize(next_local_ident);
                    next_local_ident += 1;

                    new_local
                });

                *statement_local = *local_remap;
            }
        }
    }
}

struct BasicBlockFuncArg<'a> {
    orig_local: Local,
    arg_name: String,
    param_type: Ty<'a>,
}

/// For all types that we need to return, we return a tuple of everything together.
struct BasicBlockRetParam<'a> {
    orig_local: Local,
    param_type: Ty<'a>,
}

pub(crate) fn create_funcs_from_func_bbs<'a, 'b>(
    tcx: TyCtxt<'a>,
    f_body: &Body<'a>,
    f_name: &str,
) -> Vec<GeneratedFuncInfo<'a>> {
    let live_analysis = MaybeLiveLocals;
    let mut live_cursor = live_analysis
        .iterate_to_fixpoint(tcx, f_body, Some("Function to basic block liveness check"))
        .into_results_cursor(f_body);

    // Are these BBs visited from top to bottom? Might get O(n^2) performance for worst case if going bottom up.
    let bb_func_ret_and_arg_info: Vec<_> = f_body
        .basic_blocks
        .iter_enumerated()
        .map(|(bb_key, _)| process_bb(f_body, &bb_key, &mut live_cursor))
        .collect();

    let mut next_f_id = 0;

    bb_func_ret_and_arg_info
        .into_iter()
        .enumerate()
        .map(|(i, p_bb)| {
            let bb_f_name = format!("{}_{}", f_name, i);

            let mut sig = Signature::new(CallConv::SystemV);
            sig.params.extend(p_bb.arg_and_ret_info.args.iter().map(|arg_type| {
                AbiParam::new(clif_type_from_ty(tcx, arg_type.param_type).unwrap())
            }));
            sig.returns.extend(p_bb.arg_and_ret_info.return_info.iter().map(|ret_info| {
                AbiParam::new(clif_type_from_ty(tcx, ret_info.param_type).unwrap())
            }));

            next_f_id += 1;
            let b_f_id = UserFuncName::User(UserExternalName::new(0, next_f_id));
            let func = Function::with_name_signature(b_f_id, sig);

            let bb = f_body.basic_blocks.get(p_bb.bb_key).expect("BB missing for key!");

            let mut local_replace_map = LocalReplaceMap::new(&p_bb.arg_and_ret_info);
            local_replace_map.rewrite_locals_in_bb_statements(&mut bb.statements.clone());

            let additional_term_info = create_additional_term_info(&mut live_cursor);

            GeneratedFuncInfo {
                func,
                bb_args_and_return: p_bb.arg_and_ret_info,
                additional_term_info,
                local_replace_map,
                func_name: bb_f_name,
            }
        })
        .collect()
}

fn process_bb<'a>(
    f_body: &Body<'a>,
    bb_key: &BasicBlock,
    live_cursor: &mut ResultsCursor<'_, '_, MaybeLiveLocals>,
) -> ProcessedBB<'a> {
    let arg_and_ret_info = determine_bb_func_args_and_return_type(f_body, bb_key, live_cursor);

    ProcessedBB {
        bb_key: *bb_key,
        arg_and_ret_info,
        term_info: create_additional_term_info(live_cursor),
    }
}

fn create_additional_term_info(
    cursor: &mut ResultsCursor<'_, '_, MaybeLiveLocals>,
) -> AdditionalTermInfo {
    todo!()
}

fn determine_bb_func_args_and_return_type<'a>(
    f_body: &Body<'a>,
    bb_key: &BasicBlock,
    live_cursor: &mut ResultsCursor<'_, '_, MaybeLiveLocals>,
) -> BasicBlockArgsAndReturn<'a> {
    live_cursor.seek_to_block_start(*bb_key);
    let live_in = live_cursor.get().clone();

    live_cursor.seek_to_block_end(*bb_key);
    let live_out = live_cursor.get().clone();

    // The input args are going to be whatever is live at the start of the function but dead by the end.
    let locals_that_are_args = live_in.iter().filter(|i| !live_out.contains(*i));
    let args = locals_that_are_args
        .map(|local_arg| BasicBlockFuncArg {
            orig_local: local_arg,
            arg_name: local_arg.as_u32().to_string(),
            param_type: f_body.local_decls[local_arg].ty,
        })
        .collect();

    // The output locals are going to be whatever is alive at the end but dead at the start.
    let locals_to_return = live_out.iter().filter(|o| !live_in.contains(*o));
    let return_types = locals_to_return
        .map(|ret_local| BasicBlockRetParam {
            orig_local: ret_local,
            param_type: f_body.local_decls[ret_local].ty,
        })
        .collect();

    BasicBlockArgsAndReturn { args, return_info: return_types }
}

fn extract_locals_from_statement<'a>(stmt: &Statement<'_>) -> impl Iterator<Item = &'a mut Local> {
    std::iter::empty()
}
