use rustc_abi::{BackendRepr, ExternAbi, PointerKind, Scalar, Size};
use rustc_hir::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::layout::{
    FnAbiError, HasTyCtxt, HasTypingEnv, LayoutCx, LayoutOf, TyAndLayout, fn_can_unwind,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_session::config::OptLevel;
use rustc_target::abi::Primitive::Pointer;
use rustc_target::callconv::{
    ArgAbi, ArgAttribute, ArgAttributes, ArgExtension, Conv, FnAbi, PassMode, RiscvInterruptKind,
};

// FIXME(eddyb) perhaps group the signature/type-containing (or all of them?)
// arguments of this method, into a separate `struct`.
pub(crate) fn fn_abi_new_uncached<'tcx>(
    cx: &LayoutCx<'tcx>,
    sig: ty::FnSig<'tcx>,
    extra_args: &[Ty<'tcx>],
    caller_location: Option<Ty<'tcx>>,
    fn_def_id: Option<DefId>,
    // FIXME(eddyb) replace this with something typed, like an `enum`.
    force_thin_self_ptr: bool,
) -> Result<&'tcx FnAbi<'tcx, Ty<'tcx>>, &'tcx FnAbiError<'tcx>> {
    let tcx = cx.tcx();
    let sig = tcx.normalize_erasing_regions(cx.typing_env, sig);

    let conv = conv_from_spec_abi(cx.tcx(), sig.abi, sig.c_variadic);

    let mut inputs = sig.inputs();
    let extra_args = if sig.abi == ExternAbi::RustCall {
        assert!(!sig.c_variadic && extra_args.is_empty());

        if let Some(input) = sig.inputs().last() {
            if let ty::Tuple(tupled_arguments) = input.kind() {
                inputs = &sig.inputs()[0..sig.inputs().len() - 1];
                tupled_arguments
            } else {
                bug!(
                    "argument to function with \"rust-call\" ABI \
                        is not a tuple"
                );
            }
        } else {
            bug!(
                "argument to function with \"rust-call\" ABI \
                    is not a tuple"
            );
        }
    } else {
        assert!(sig.c_variadic || extra_args.is_empty());
        extra_args
    };

    let is_drop_in_place =
        fn_def_id.is_some_and(|def_id| tcx.is_lang_item(def_id, LangItem::DropInPlace));

    let arg_of = |ty: Ty<'tcx>, arg_idx: Option<usize>| -> Result<_, &'tcx FnAbiError<'tcx>> {
        let span = tracing::debug_span!("arg_of");
        let _entered = span.enter();
        let is_return = arg_idx.is_none();
        let is_drop_target = is_drop_in_place && arg_idx == Some(0);
        let drop_target_pointee = is_drop_target.then(|| match ty.kind() {
            ty::RawPtr(ty, _) => *ty,
            _ => bug!("argument to drop_in_place is not a raw ptr: {:?}", ty),
        });

        let layout = cx.layout_of(ty).map_err(|err| &*tcx.arena.alloc(FnAbiError::Layout(*err)))?;
        let layout = if force_thin_self_ptr && arg_idx == Some(0) {
            // Don't pass the vtable, it's not an argument of the virtual fn.
            // Instead, pass just the data pointer, but give it the type `*const/mut dyn Trait`
            // or `&/&mut dyn Trait` because this is special-cased elsewhere in codegen
            make_thin_self_ptr(cx, layout)
        } else {
            layout
        };

        let mut arg = ArgAbi::new(cx, layout, |layout, scalar, offset| {
            let mut attrs = ArgAttributes::new();
            adjust_for_rust_scalar(
                *cx,
                &mut attrs,
                scalar,
                *layout,
                offset,
                is_return,
                drop_target_pointee,
            );
            attrs
        });

        if arg.layout.is_zst() {
            arg.mode = PassMode::Ignore;
        }

        Ok(arg)
    };

    let mut fn_abi = FnAbi {
        ret: arg_of(sig.output(), None)?,
        args: inputs
            .iter()
            .copied()
            .chain(extra_args.iter().copied())
            .chain(caller_location)
            .enumerate()
            .map(|(i, ty)| arg_of(ty, Some(i)))
            .collect::<Result<_, _>>()?,
        c_variadic: sig.c_variadic,
        fixed_count: inputs.len() as u32,
        conv,
        can_unwind: fn_can_unwind(cx.tcx(), fn_def_id, sig.abi),
    };
    fn_abi_adjust_for_abi(cx, &mut fn_abi, sig.abi, fn_def_id)?;
    debug!("fn_abi_new_uncached = {:?}", fn_abi);
    fn_abi_sanity_check(cx, &fn_abi, sig.abi);
    Ok(tcx.arena.alloc(fn_abi))
}

// Handle safe Rust thin and wide pointers.
fn adjust_for_rust_scalar<'tcx>(
    cx: LayoutCx<'tcx>,
    attrs: &mut ArgAttributes,
    scalar: Scalar,
    layout: TyAndLayout<'tcx>,
    offset: Size,
    is_return: bool,
    drop_target_pointee: Option<Ty<'tcx>>,
) {
    // Booleans are always a noundef i1 that needs to be zero-extended.
    if scalar.is_bool() {
        attrs.ext(ArgExtension::Zext);
        attrs.set(ArgAttribute::NoUndef);
        return;
    }

    if !scalar.is_uninit_valid() {
        attrs.set(ArgAttribute::NoUndef);
    }

    // Only pointer types handled below.
    let Scalar::Initialized { value: Pointer(_), valid_range } = scalar else { return };

    // Set `nonnull` if the validity range excludes zero, or for the argument to `drop_in_place`,
    // which must be nonnull per its documented safety requirements.
    if !valid_range.contains(0) || drop_target_pointee.is_some() {
        attrs.set(ArgAttribute::NonNull);
    }

    let tcx = cx.tcx();

    if let Some(pointee) = layout.pointee_info_at(&cx, offset) {
        let kind = if let Some(kind) = pointee.safe {
            Some(kind)
        } else if let Some(pointee) = drop_target_pointee {
            // The argument to `drop_in_place` is semantically equivalent to a mutable reference.
            Some(PointerKind::MutableRef { unpin: pointee.is_unpin(tcx, cx.typing_env) })
        } else {
            None
        };
        if let Some(kind) = kind {
            attrs.pointee_align = Some(pointee.align);

            // `Box` are not necessarily dereferenceable for the entire duration of the function as
            // they can be deallocated at any time. Same for non-frozen shared references (see
            // <https://github.com/rust-lang/rust/pull/98017>), and for mutable references to
            // potentially self-referential types (see
            // <https://github.com/rust-lang/unsafe-code-guidelines/issues/381>). If LLVM had a way
            // to say "dereferenceable on entry" we could use it here.
            attrs.pointee_size = match kind {
                PointerKind::Box { .. }
                | PointerKind::SharedRef { frozen: false }
                | PointerKind::MutableRef { unpin: false } => Size::ZERO,
                PointerKind::SharedRef { frozen: true }
                | PointerKind::MutableRef { unpin: true } => pointee.size,
            };

            // The aliasing rules for `Box<T>` are still not decided, but currently we emit
            // `noalias` for it. This can be turned off using an unstable flag.
            // See https://github.com/rust-lang/unsafe-code-guidelines/issues/326
            let noalias_for_box = tcx.sess.opts.unstable_opts.box_noalias;

            // LLVM prior to version 12 had known miscompiles in the presence of noalias attributes
            // (see #54878), so it was conditionally disabled, but we don't support earlier
            // versions at all anymore. We still support turning it off using -Zmutable-noalias.
            let noalias_mut_ref = tcx.sess.opts.unstable_opts.mutable_noalias;

            // `&T` where `T` contains no `UnsafeCell<U>` is immutable, and can be marked as both
            // `readonly` and `noalias`, as LLVM's definition of `noalias` is based solely on memory
            // dependencies rather than pointer equality. However this only applies to arguments,
            // not return values.
            //
            // `&mut T` and `Box<T>` where `T: Unpin` are unique and hence `noalias`.
            let no_alias = match kind {
                PointerKind::SharedRef { frozen } => frozen,
                PointerKind::MutableRef { unpin } => unpin && noalias_mut_ref,
                PointerKind::Box { unpin, global } => unpin && global && noalias_for_box,
            };
            // We can never add `noalias` in return position; that LLVM attribute has some very surprising semantics
            // (see <https://github.com/rust-lang/unsafe-code-guidelines/issues/385#issuecomment-1368055745>).
            if no_alias && !is_return {
                attrs.set(ArgAttribute::NoAlias);
            }

            if matches!(kind, PointerKind::SharedRef { frozen: true }) && !is_return {
                attrs.set(ArgAttribute::ReadOnly);
            }
        }
    }
}

fn fn_abi_adjust_for_abi<'tcx>(
    cx: &LayoutCx<'tcx>,
    fn_abi: &mut FnAbi<'tcx, Ty<'tcx>>,
    abi: ExternAbi,
    fn_def_id: Option<DefId>,
) -> Result<(), &'tcx FnAbiError<'tcx>> {
    if abi == ExternAbi::Unadjusted {
        // The "unadjusted" ABI passes aggregates in "direct" mode. That's fragile but needed for
        // some LLVM intrinsics.
        fn unadjust<'tcx>(arg: &mut ArgAbi<'tcx, Ty<'tcx>>) {
            // This still uses `PassMode::Pair` for ScalarPair types. That's unlikely to be intended,
            // but who knows what breaks if we change this now.
            if matches!(arg.layout.backend_repr, BackendRepr::Memory { .. }) {
                assert!(
                    arg.layout.backend_repr.is_sized(),
                    "'unadjusted' ABI does not support unsized arguments"
                );
            }
            arg.make_direct_deprecated();
        }

        unadjust(&mut fn_abi.ret);
        for arg in fn_abi.args.iter_mut() {
            unadjust(arg);
        }
        return Ok(());
    }

    let tcx = cx.tcx();

    if abi == ExternAbi::Rust || abi == ExternAbi::RustCall || abi == ExternAbi::RustIntrinsic {
        fn_abi.adjust_for_rust_abi(cx, abi);

        // Look up the deduced parameter attributes for this function, if we have its def ID and
        // we're optimizing in non-incremental mode. We'll tag its parameters with those attributes
        // as appropriate.
        let deduced_param_attrs =
            if tcx.sess.opts.optimize != OptLevel::No && tcx.sess.opts.incremental.is_none() {
                fn_def_id.map(|fn_def_id| tcx.deduced_param_attrs(fn_def_id)).unwrap_or_default()
            } else {
                &[]
            };

        for (arg_idx, arg) in fn_abi.args.iter_mut().enumerate() {
            if arg.is_ignore() {
                continue;
            }

            // If we deduced that this parameter was read-only, add that to the attribute list now.
            //
            // The `readonly` parameter only applies to pointers, so we can only do this if the
            // argument was passed indirectly. (If the argument is passed directly, it's an SSA
            // value, so it's implicitly immutable.)
            if let &mut PassMode::Indirect { ref mut attrs, .. } = &mut arg.mode {
                // The `deduced_param_attrs` list could be empty if this is a type of function
                // we can't deduce any parameters for, so make sure the argument index is in
                // bounds.
                if let Some(deduced_param_attrs) = deduced_param_attrs.get(arg_idx) {
                    if deduced_param_attrs.read_only {
                        attrs.regular.insert(ArgAttribute::ReadOnly);
                        debug!("added deduced read-only attribute");
                    }
                }
            }
        }
    } else {
        fn_abi
            .adjust_for_foreign_abi(cx, abi)
            .map_err(|err| &*tcx.arena.alloc(FnAbiError::AdjustForForeignAbi(err)))?;
    }

    Ok(())
}

/// Ensure that the ABI makes basic sense.
fn fn_abi_sanity_check<'tcx>(
    cx: &LayoutCx<'tcx>,
    fn_abi: &FnAbi<'tcx, Ty<'tcx>>,
    spec_abi: ExternAbi,
) {
    fn fn_arg_sanity_check<'tcx>(
        cx: &LayoutCx<'tcx>,
        fn_abi: &FnAbi<'tcx, Ty<'tcx>>,
        spec_abi: ExternAbi,
        arg: &ArgAbi<'tcx, Ty<'tcx>>,
    ) {
        let tcx = cx.tcx();

        if spec_abi == ExternAbi::Rust
            || spec_abi == ExternAbi::RustCall
            || spec_abi == ExternAbi::RustCold
        {
            if arg.layout.is_zst() {
                // Casting closures to function pointers depends on ZST closure types being
                // omitted entirely in the calling convention.
                assert!(arg.is_ignore());
            }
            if let PassMode::Indirect { on_stack, .. } = arg.mode {
                assert!(!on_stack, "rust abi shouldn't use on_stack");
            }
        }

        match &arg.mode {
            PassMode::Ignore => {
                assert!(arg.layout.is_zst() || arg.layout.is_uninhabited());
            }
            PassMode::Direct(_) => {
                // Here the Rust type is used to determine the actual ABI, so we have to be very
                // careful. Scalar/Vector is fine, since backends will generally use
                // `layout.backend_repr` and ignore everything else. We should just reject
                //`Aggregate` entirely here, but some targets need to be fixed first.
                match arg.layout.backend_repr {
                    BackendRepr::Uninhabited
                    | BackendRepr::Scalar(_)
                    | BackendRepr::Vector { .. } => {}
                    BackendRepr::ScalarPair(..) => {
                        panic!("`PassMode::Direct` used for ScalarPair type {}", arg.layout.ty)
                    }
                    BackendRepr::Memory { sized } => {
                        // For an unsized type we'd only pass the sized prefix, so there is no universe
                        // in which we ever want to allow this.
                        assert!(sized, "`PassMode::Direct` for unsized type in ABI: {:#?}", fn_abi);
                        // This really shouldn't happen even for sized aggregates, since
                        // `immediate_llvm_type` will use `layout.fields` to turn this Rust type into an
                        // LLVM type. This means all sorts of Rust type details leak into the ABI.
                        // However wasm sadly *does* currently use this mode for it's "C" ABI so we
                        // have to allow it -- but we absolutely shouldn't let any more targets do
                        // that. (Also see <https://github.com/rust-lang/rust/issues/115666>.)
                        //
                        // The unstable abi `PtxKernel` also uses Direct for now.
                        // It needs to switch to something else before stabilization can happen.
                        // (See issue: https://github.com/rust-lang/rust/issues/117271)
                        //
                        // And finally the unadjusted ABI is ill specified and uses Direct for all
                        // args, but unfortunately we need it for calling certain LLVM intrinsics.

                        match spec_abi {
                            ExternAbi::Unadjusted => {}
                            ExternAbi::PtxKernel => {}
                            ExternAbi::C { unwind: _ }
                                if matches!(&*tcx.sess.target.arch, "wasm32" | "wasm64") => {}
                            _ => {
                                panic!(
                                    "`PassMode::Direct` for aggregates only allowed for \"unadjusted\" and \"ptx-kernel\" functions and on wasm\n\
                                      Problematic type: {:#?}",
                                    arg.layout,
                                );
                            }
                        }
                    }
                }
            }
            PassMode::Pair(_, _) => {
                // Similar to `Direct`, we need to make sure that backends use `layout.backend_repr`
                // and ignore the rest of the layout.
                assert!(
                    matches!(arg.layout.backend_repr, BackendRepr::ScalarPair(..)),
                    "PassMode::Pair for type {}",
                    arg.layout.ty
                );
            }
            PassMode::Cast { .. } => {
                // `Cast` means "transmute to `CastType`"; that only makes sense for sized types.
                assert!(arg.layout.is_sized());
            }
            PassMode::Indirect { meta_attrs: None, .. } => {
                // No metadata, must be sized.
                // Conceptually, unsized arguments must be copied around, which requires dynamically
                // determining their size, which we cannot do without metadata. Consult
                // t-opsem before removing this check.
                assert!(arg.layout.is_sized());
            }
            PassMode::Indirect { meta_attrs: Some(_), on_stack, .. } => {
                // With metadata. Must be unsized and not on the stack.
                assert!(arg.layout.is_unsized() && !on_stack);
                // Also, must not be `extern` type.
                let tail = tcx.struct_tail_for_codegen(arg.layout.ty, cx.typing_env);
                if matches!(tail.kind(), ty::Foreign(..)) {
                    // These types do not have metadata, so having `meta_attrs` is bogus.
                    // Conceptually, unsized arguments must be copied around, which requires dynamically
                    // determining their size. Therefore, we cannot allow `extern` types here. Consult
                    // t-opsem before removing this check.
                    panic!("unsized arguments must not be `extern` types");
                }
            }
        }
    }

    for arg in fn_abi.args.iter() {
        fn_arg_sanity_check(cx, fn_abi, spec_abi, arg);
    }
    fn_arg_sanity_check(cx, fn_abi, spec_abi, &fn_abi.ret);
}

fn make_thin_self_ptr<'tcx>(
    cx: &(impl HasTyCtxt<'tcx> + HasTypingEnv<'tcx>),
    layout: TyAndLayout<'tcx>,
) -> TyAndLayout<'tcx> {
    let tcx = cx.tcx();
    let wide_pointer_ty = if layout.is_unsized() {
        // unsized `self` is passed as a pointer to `self`
        // FIXME (mikeyhew) change this to use &own if it is ever added to the language
        Ty::new_mut_ptr(tcx, layout.ty)
    } else {
        match layout.backend_repr {
            BackendRepr::ScalarPair(..) | BackendRepr::Scalar(..) => (),
            _ => bug!("receiver type has unsupported layout: {:?}", layout),
        }

        // In the case of Rc<Self>, we need to explicitly pass a *mut RcInner<Self>
        // with a Scalar (not ScalarPair) ABI. This is a hack that is understood
        // elsewhere in the compiler as a method on a `dyn Trait`.
        // To get the type `*mut RcInner<Self>`, we just keep unwrapping newtypes until we
        // get a built-in pointer type
        let mut wide_pointer_layout = layout;
        while !wide_pointer_layout.ty.is_unsafe_ptr() && !wide_pointer_layout.ty.is_ref() {
            wide_pointer_layout = wide_pointer_layout
                .non_1zst_field(cx)
                .expect("not exactly one non-1-ZST field in a `DispatchFromDyn` type")
                .1
        }

        wide_pointer_layout.ty
    };

    // we now have a type like `*mut RcInner<dyn Trait>`
    // change its layout to that of `*mut ()`, a thin pointer, but keep the same type
    // this is understood as a special case elsewhere in the compiler
    let unit_ptr_ty = Ty::new_mut_ptr(tcx, tcx.types.unit);

    TyAndLayout {
        ty: wide_pointer_ty,

        // NOTE(eddyb) using an empty `ParamEnv`, and `unwrap`-ing the `Result`
        // should always work because the type is always `*mut ()`.
        ..tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(unit_ptr_ty)).unwrap()
    }
}

#[inline]
fn conv_from_spec_abi(tcx: TyCtxt<'_>, abi: ExternAbi, c_variadic: bool) -> Conv {
    use rustc_abi::ExternAbi::*;
    match tcx.sess.target.adjust_abi(abi, c_variadic) {
        RustIntrinsic | Rust | RustCall => Conv::Rust,

        // This is intentionally not using `Conv::Cold`, as that has to preserve
        // even SIMD registers, which is generally not a good trade-off.
        RustCold => Conv::PreserveMost,

        // It's the ABI's job to select this, not ours.
        System { .. } => bug!("system abi should be selected elsewhere"),
        EfiApi => bug!("eficall abi should be selected elsewhere"),

        Stdcall { .. } => Conv::X86Stdcall,
        Fastcall { .. } => Conv::X86Fastcall,
        Vectorcall { .. } => Conv::X86VectorCall,
        Thiscall { .. } => Conv::X86ThisCall,
        C { .. } => Conv::C,
        Unadjusted => Conv::C,
        Win64 { .. } => Conv::X86_64Win64,
        SysV64 { .. } => Conv::X86_64SysV,
        Aapcs { .. } => Conv::ArmAapcs,
        CCmseNonSecureCall => Conv::CCmseNonSecureCall,
        CCmseNonSecureEntry => Conv::CCmseNonSecureEntry,
        PtxKernel => Conv::PtxKernel,
        Msp430Interrupt => Conv::Msp430Intr,
        X86Interrupt => Conv::X86Intr,
        GpuKernel => Conv::GpuKernel,
        AvrInterrupt => Conv::AvrInterrupt,
        AvrNonBlockingInterrupt => Conv::AvrNonBlockingInterrupt,
        RiscvInterruptM => Conv::RiscvInterrupt { kind: RiscvInterruptKind::Machine },
        RiscvInterruptS => Conv::RiscvInterrupt { kind: RiscvInterruptKind::Supervisor },

        // These API constants ought to be more specific...
        Cdecl { .. } => Conv::C,
    }
}
