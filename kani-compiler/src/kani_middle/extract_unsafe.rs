use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};

use tracing::debug;

use std::ops::Bound;

pub struct UnsafetyExtractor<'a, 'tcx> {
    body: &'a Body<'tcx>,
    body_did: LocalDefId,
    source_info: SourceInfo,
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,

    // Occurrences of unsafe:
    raw_pointer_derefs: Vec<SourceInfo>,
    // TODO: add other types of unsafe
}

impl<'a, 'tcx> UnsafetyExtractor<'a, 'tcx> {
    fn new(
        body: &'a Body<'tcx>,
        body_did: LocalDefId,
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
    ) -> Self {
        Self {
            body,
            body_did,
            source_info: SourceInfo::outermost(body.span),
            tcx,
            param_env,
            raw_pointer_derefs: Vec::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for UnsafetyExtractor<'_, 'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.source_info = terminator.source_info;
        match terminator.kind {
            TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Drop { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::GeneratorDrop
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => {
                // safe (at least as emitted during MIR construction)
            }

            TerminatorKind::Call { ref func, .. } => {
                let func_ty = func.ty(self.body, self.tcx);
                let func_id =
                    if let ty::FnDef(func_id, _) = func_ty.kind() { Some(func_id) } else { None };
                let sig = func_ty.fn_sig(self.tcx);
                if let hir::Unsafety::Unsafe = sig.unsafety() {
                    self.store_unsafe(UnsafetyViolationDetails::CallToUnsafeFunction)
                }

                if let Some(func_id) = func_id {
                    self.check_target_features(*func_id);
                }
            }

            TerminatorKind::InlineAsm { .. } => {
                self.store_unsafe(UnsafetyViolationDetails::UseOfInlineAssembly)
            }
        }
        self.super_terminator(terminator, location);
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.source_info = statement.source_info;
        match statement.kind {
            StatementKind::Assign(..)
            | StatementKind::FakeRead(..)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::Deinit(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Retag { .. }
            | StatementKind::PlaceMention(..)
            | StatementKind::Coverage(..)
            | StatementKind::Intrinsic(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => {
                // safe (at least as emitted during MIR construction)
            }
            // `AscribeUserType` just exists to help MIR borrowck.
            // It has no semantics, and everything is already reported by `PlaceMention`.
            StatementKind::AscribeUserType(..) => return,
        }
        self.super_statement(statement, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Aggregate(box ref aggregate, _) => match aggregate {
                &AggregateKind::Array(..) | &AggregateKind::Tuple => {}
                &AggregateKind::Adt(adt_did, ..) => {
                    match self.tcx.layout_scalar_valid_range(adt_did) {
                        (Bound::Unbounded, Bound::Unbounded) => {}
                        _ => self.store_unsafe(UnsafetyViolationDetails::InitializingTypeWith),
                    }
                }
                &AggregateKind::Closure(def_id, _) | &AggregateKind::Generator(def_id, _, _) => {
                    let _def_id = def_id.expect_local();
                }
            },
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_operand(&mut self, op: &Operand<'tcx>, location: Location) {
        if let Operand::Constant(constant) = op {
            let maybe_uneval = match constant.literal {
                ConstantKind::Val(..) | ConstantKind::Ty(_) => None,
                ConstantKind::Unevaluated(uv, _) => Some(uv),
            };

            if let Some(uv) = maybe_uneval {
                if uv.promoted.is_none() {
                    let def_id = uv.def;
                    if self.tcx.def_kind(def_id) == DefKind::InlineConst {
                        let _local_def_id = def_id.expect_local();
                    }
                }
            }
        }
        self.super_operand(op, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
        // On types with `scalar_valid_range`, prevent
        // * `&mut x.field`
        // * `x.field = y;`
        // * `&x.field` if `field`'s type has interior mutability
        // because either of these would allow modifying the layout constrained field and
        // insert values that violate the layout constraints.
        if context.is_mutating_use() || context.is_borrow() {
            self.check_mut_borrowing_layout_constrained_field(*place, context.is_mutating_use());
        }

        // Some checks below need the extra meta info of the local declaration.
        let decl = &self.body.local_decls[place.local];

        // Check the base local: it might be an unsafe-to-access static. We only check derefs of the
        // temporary holding the static pointer to avoid duplicate errors
        // <https://github.com/rust-lang/rust/pull/78068#issuecomment-731753506>.
        if decl.internal && place.projection.first() == Some(&ProjectionElem::Deref) {
            // If the projection root is an artificial local that we introduced when
            // desugaring `static`, give a more specific error message
            // (avoid the general "raw pointer" clause below, that would only be confusing).
            if let LocalInfo::StaticRef { def_id, .. } = *decl.local_info() {
                if self.tcx.is_mutable_static(def_id) {
                    self.store_unsafe(UnsafetyViolationDetails::UseOfMutableStatic);
                    return;
                } else if self.tcx.is_foreign_item(def_id) {
                    self.store_unsafe(UnsafetyViolationDetails::UseOfExternStatic);
                    return;
                }
            }
        }

        // Check for raw pointer `Deref`.
        for (base, proj) in place.iter_projections() {
            if proj == ProjectionElem::Deref {
                let base_ty = base.ty(self.body, self.tcx).ty;
                if base_ty.is_unsafe_ptr() {
                    self.store_unsafe(UnsafetyViolationDetails::DerefOfRawPointer)
                }
            }
        }

        // Check for union fields. For this we traverse right-to-left, as the last `Deref` changes
        // whether we *read* the union field or potentially *write* to it (if this place is being assigned to).
        let mut saw_deref = false;
        for (base, proj) in place.iter_projections().rev() {
            if proj == ProjectionElem::Deref {
                saw_deref = true;
                continue;
            }

            let base_ty = base.ty(self.body, self.tcx).ty;
            if base_ty.is_union() {
                // If we did not hit a `Deref` yet and the overall place use is an assignment, the
                // rules are different.
                let assign_to_field = !saw_deref
                    && matches!(
                        context,
                        PlaceContext::MutatingUse(
                            MutatingUseContext::Store
                                | MutatingUseContext::Drop
                                | MutatingUseContext::AsmOutput
                        )
                    );
                // If this is just an assignment, determine if the assigned type needs dropping.
                if assign_to_field {
                    // We have to check the actual type of the assignment, as that determines if the
                    // old value is being dropped.
                    let assigned_ty = place.ty(&self.body.local_decls, self.tcx).ty;
                    if assigned_ty.needs_drop(self.tcx, self.param_env) {
                        // This would be unsafe, but should be outright impossible since we reject such unions.
                        self.tcx.sess.delay_span_bug(
                            self.source_info.span,
                            format!("union fields that need dropping should be impossible: {assigned_ty}")
                        );
                    }
                } else {
                    self.store_unsafe(UnsafetyViolationDetails::AccessToUnionField)
                }
            }
        }
    }
}

impl<'tcx> UnsafetyExtractor<'_, 'tcx> {
    fn store_unsafe(&mut self, details: UnsafetyViolationDetails) {
        match details {
            UnsafetyViolationDetails::DerefOfRawPointer => {
                self.raw_pointer_derefs.push(self.source_info)
            }
            _ => println!("TODO: handle {details:?}"),
        }
    }

    fn check_mut_borrowing_layout_constrained_field(
        &mut self,
        place: Place<'tcx>,
        is_mut_use: bool,
    ) {
        for (place_base, elem) in place.iter_projections().rev() {
            match elem {
                // Modifications behind a dereference don't affect the value of
                // the pointer.
                ProjectionElem::Deref => return,
                ProjectionElem::Field(..) => {
                    let ty = place_base.ty(&self.body.local_decls, self.tcx).ty;
                    if let ty::Adt(def, _) = ty.kind() {
                        if self.tcx.layout_scalar_valid_range(def.did())
                            != (Bound::Unbounded, Bound::Unbounded)
                        {
                            let details = if is_mut_use {
                                UnsafetyViolationDetails::MutationOfLayoutConstrainedField

                            // Check `is_freeze` as late as possible to avoid cycle errors
                            // with opaque types.
                            } else if !place
                                .ty(self.body, self.tcx)
                                .ty
                                .is_freeze(self.tcx, self.param_env)
                            {
                                UnsafetyViolationDetails::BorrowOfLayoutConstrainedField
                            } else {
                                continue;
                            };
                            self.store_unsafe(details);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Checks whether calling `func_did` needs an `unsafe` context or not, i.e. whether
    /// the called function has target features the calling function hasn't.
    fn check_target_features(&mut self, func_did: DefId) {
        // Unsafety isn't required on wasm targets. For more information see
        // the corresponding check in typeck/src/collect.rs
        if self.tcx.sess.target.options.is_like_wasm {
            return;
        }

        let callee_features = &self.tcx.codegen_fn_attrs(func_did).target_features;
        // The body might be a constant, so it doesn't have codegen attributes.
        let self_features = &self.tcx.body_codegen_attrs(self.body_did.to_def_id()).target_features;

        // Is `callee_features` a subset of `calling_features`?
        if !callee_features.iter().all(|feature| self_features.contains(feature)) {
            self.store_unsafe(UnsafetyViolationDetails::CallToFunctionWith)
        }
    }
}

pub fn extract_unsafety<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &Body<'tcx>) {
    debug!("extract_unsafety({:?})", def);

    let param_env = tcx.param_env(def);

    let mut extractor = UnsafetyExtractor::new(body, def, tcx, param_env);
    extractor.visit_body(&body);

    // report results
    println!("{:?}", extractor.raw_pointer_derefs);
}
