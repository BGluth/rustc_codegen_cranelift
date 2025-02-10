//! Scan all of a function's BBs and determine the read/write deps for each.

use std::collections::{HashMap, HashSet};

use cranelift_codegen::ir::Function;
use rustc_index::bit_set::{DenseBitSet, GrowableBitSet};
use rustc_middle::mir::{BasicBlock, Body, HasLocalDecls, Local};
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_mir_dataflow::impls::MaybeLiveLocals;
use rustc_mir_dataflow::{Analysis, JoinSemiLattice, ResultsCursor};

enum TerminatorType {
    Call,

    /// From branch.
    MultiCall,
    Return,
}

#[derive(Debug)]
pub(super) struct BBReadWriteInfo {
    pub(super) reads: HashSet<Local>,
    pub(super) writes: HashSet<Local>,
}

struct BasicBlockWithMeta {
    key: BasicBlock,
    read_write_info: BBReadWriteInfo,
    term_type: TerminatorType,
}

struct BasicBlockArgsAndReturn<'a> {
    args: Vec<BasicBlockFuncArg<'a>>,
    return_types: Vec<Ty<'a>>,
}

struct BasicBlockFuncArg<'a> {
    arg_name: String,
    arg_type: Ty<'a>,
}

pub(super) fn create_funcs_from_func_bbs<'a>(tcx: TyCtxt<'a>, f_body: &Body<'a>) -> Vec<Function> {
    let live_analysis = MaybeLiveLocals;
    let mut live_cursor = live_analysis
        .iterate_to_fixpoint(tcx, f_body, Some("Function to basic block liveness check"))
        .into_results_cursor(f_body);

    // Are these BBs visited from top to bottom? Might get O(n^2) performance for worst case if going bottom up.
    let bb_func_out_args: Vec<_> = f_body
        .basic_blocks
        .iter_enumerated()
        .map(|(bb_key, _)| {
            determine_bb_func_args_and_return_type(f_body, &bb_key, &mut live_cursor)
        })
        .collect();

    todo!()
}

fn create_bb_usages_per_func(f_body: &Body) -> HashMap<BasicBlock, BBReadWriteInfo> {
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
            arg_name: local_arg.as_u32().to_string(),
            arg_type: f_body.local_decls[local_arg].ty,
        })
        .collect();

    // The output locals are going to be whatever is alive at the end but dead at the start.
    let locals_to_return = live_out.iter().filter(|o| !live_in.contains(*o));
    let return_types = locals_to_return.map(|ret_local| f_body.local_decls[ret_local].ty).collect();

    BasicBlockArgsAndReturn { args, return_types }
}

fn convert_bbs_to_funcs(bbs: &[BasicBlockWithMeta]) -> Vec<Function> {
    todo!()
}
