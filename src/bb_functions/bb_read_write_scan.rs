//! Scan all of a function's BBs and determine the read/write deps for each.

use std::collections::HashMap;

use cranelift_codegen::ir::{AbiParam, Function, Signature, UserExternalName, UserFuncName};
use cranelift_codegen::isa::CallConv;
use rustc_middle::mir::{BasicBlock, Body, Local, Statement};
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_mir_dataflow::impls::MaybeLiveLocals;
use rustc_mir_dataflow::{Analysis, ResultsCursor};

use crate::FunctionCx;

enum TerminatorType {
    Call,

    /// From branch.
    MultiCall,
    Return,
}

pub(crate) struct GeneratedFuncInfo<'a> {
    func: Function,
    ret_types: Vec<BasicBlockRetParam<'a>>,
}

struct ProcessedBB<'a> {
    bb_key: BasicBlock,
    arg_and_ret_info: BasicBlockArgsAndReturn<'a>,
    term_type: TerminatorType,
}

struct BasicBlockArgsAndReturn<'a> {
    args: Vec<BasicBlockFuncArg<'a>>,
    return_types: Vec<BasicBlockRetParam<'a>>,
}

struct LocalReplaceMap {
    map: HashMap<Local, Local>,
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

        for ret_info in arg_and_ret_info.return_types.iter() {
            map.insert(ret_info.local, Local::from_usize(next_local_ident));
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
    local: Local,
    param_type: Ty<'a>,
}

pub(super) fn create_funcs_from_func_bbs<'a>(
    tcx: TyCtxt<'a>,
    f_name: &str,
    f_body: &Body<'a>,
    f_context: &'a mut FunctionCx<'a, '_, 'a>,
    next_f_id: &mut u32,
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

    bb_func_ret_and_arg_info
        .into_iter()
        .enumerate()
        .map(|(i, p_bb)| {
            let mut sig = Signature::new(CallConv::SystemV);
            sig.params.extend(
                p_bb.arg_and_ret_info.args.iter().map(|arg_type| {
                    AbiParam::new(f_context.clif_type(arg_type.param_type).unwrap())
                }),
            );
            sig.returns.extend(
                p_bb.arg_and_ret_info.return_types.iter().map(|ret_info| {
                    AbiParam::new(f_context.clif_type(ret_info.param_type).unwrap())
                }),
            );

            *next_f_id += 1;
            let b_f_name = UserFuncName::User(UserExternalName::new(0, *next_f_id));
            let func = Function::with_name_signature(b_f_name, sig);

            let bb = f_body.basic_blocks.get(p_bb.bb_key).expect("BB missing for key!");

            let mut local_replace_map = LocalReplaceMap::new(&p_bb.arg_and_ret_info);
            local_replace_map.rewrite_locals_in_bb_statements(&mut bb.statements.clone());

            GeneratedFuncInfo { func, ret_types: p_bb.arg_and_ret_info.return_types }
        })
        .collect()
}

fn process_bb<'a>(
    f_body: &Body<'a>,
    bb_key: &BasicBlock,
    live_cursor: &mut ResultsCursor<'_, '_, MaybeLiveLocals>,
) -> ProcessedBB<'a> {
    let arg_and_ret_info = determine_bb_func_args_and_return_type(f_body, bb_key, live_cursor);

    ProcessedBB { bb_key: *bb_key, arg_and_ret_info, term_type: determine_term_type(live_cursor) }
}

fn determine_term_type(cursor: &mut ResultsCursor<'_, '_, MaybeLiveLocals>) -> TerminatorType {
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
            local: ret_local,
            param_type: f_body.local_decls[ret_local].ty,
        })
        .collect();

    BasicBlockArgsAndReturn { args, return_types }
}

fn extract_locals_from_statement<'a>(stmt: &Statement<'_>) -> impl Iterator<Item = &'a mut Local> {
    std::iter::empty()
}
