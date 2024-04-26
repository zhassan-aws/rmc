use llbc::common::*;
use llbc::formatter::AstFormatter;
use llbc::formatter::IntoFormatter;
use llbc::gast::*;
use llbc::meta::Meta;
use crate::codegen_aeneas_llbc::translate::translate_ctx::*;
use llbc::types::*;
use llbc_macros::{EnumAsGetters, EnumIsA, EnumToGetters};
use llbc::trace;
use rustc_hir::def_id::DefId;

/// Same as [TraitClause], but where the clause id is a [TraitInstanceId].
/// We need this information to solve the provenance of traits coming from
/// where clauses: when translating the where clauses and adding them to the
/// context, we recursively explore their parent/item clauses.
///
/// We have to do this because of this kind of situations
///```text
/// trait Foo {
///   type W: Bar // Bar contains a method bar
/// }
///
/// fn f<T : Foo>(x : T::W) {
///   x.bar(); // We need to refer to the trait clause declared for Foo::W
///            // and this clause is not immediately accessible.
/// }
///
/// trait FooChild : Foo {}
///
/// fn g<T : FooChild>(x: <T as Foo>::W) { ... }
///                       ^^^^^^^^^^^^^
/// //     We need to have access to a clause `FooChild : Foo` to solve this
/// ```
#[derive(Debug, Clone)]
pub(crate) struct NonLocalTraitClause {
    pub clause_id: TraitInstanceId,
    /// [Some] if this is the top clause, [None] if this is about a parent/
    /// associated type clause.
    pub meta: Option<Meta>,
    pub trait_id: TraitDeclId::Id,
    pub generics: GenericArgs,
}

impl NonLocalTraitClause {
    pub(crate) fn to_local_trait_clause(&self) -> Option<TraitClause> {
        if let TraitInstanceId::Clause(id) = &self.clause_id {
            Some(TraitClause {
                clause_id: *id,
                meta: self.meta,
                trait_id: self.trait_id,
                generics: self.generics.clone(),
            })
        } else {
            None
        }
    }

    pub(crate) fn to_trait_clause_with_id(
        &self,
        get_id: &dyn Fn(&TraitInstanceId) -> Option<TraitClauseId::Id>,
    ) -> Option<TraitClause> {
        get_id(&self.clause_id).map(|clause_id| TraitClause {
            clause_id,
            meta: self.meta,
            trait_id: self.trait_id,
            generics: self.generics.clone(),
        })
    }

    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let clause_id = self.clause_id.fmt_with_ctx(ctx);
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_id}{generics}")
    }
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, EnumToGetters)]
pub(crate) enum Predicate {
    Trait(NonLocalTraitClause),
    TypeOutlives(TypeOutlives),
    RegionOutlives(RegionOutlives),
    TraitType(TraitTypeConstraint),
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    pub(crate) fn get_parent_params_info(
        &mut self,
        _def_id: DefId,
    ) -> Result<Option<ParamsInfo>, Error> {
        Ok(None)
    }

    /// This function should be called **after** we translated the generics
    /// (type parameters, regions...).
    ///
    /// [parent_predicates_as_parent_clauses]: if [Some], the predicates
    /// of the parent must be registered as parent clauses.
    pub(crate) fn translate_predicates_of(
        &mut self,
        _parent_trait_id: Option<TraitDeclId::Id>,
        def_id: DefId,
    ) -> Result<(), Error> {
        trace!("def_id: {:?}", def_id);
        let tcx = self.t_ctx.tcx;

        //let fmt_ctx = self.into_fmt();
        Ok(())
    }

    /// Translate the predicates then solve the unsolved trait obligations
    /// in the registered trait clauses.
    pub(crate) fn translate_predicates_solve_trait_obligations_of(
        &mut self,
        parent_trait_id: Option<TraitDeclId::Id>,
        def_id: DefId,
    ) -> Result<(), Error> {
        let span = self.t_ctx.tcx.def_span(def_id);
        self.while_registering_trait_clauses(move |ctx| {
            ctx.translate_predicates_of(parent_trait_id, def_id)?;
            ctx.solve_trait_obligations_in_trait_clauses(span);
            Ok(())
        })
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    fn match_trait_clauses(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs,
        clause: &NonLocalTraitClause,
    ) -> bool {
        let fmt_ctx = self.into_fmt();
        trace!("Matching trait clauses:\n- trait_id: {:?}\n- generics: {:?}\n- clause.trait_id: {:?}\n- clause.generics: {:?}",
               fmt_ctx.format_object(trait_id), generics.fmt_with_ctx(&fmt_ctx),
               fmt_ctx.format_object(clause.trait_id), clause.generics.fmt_with_ctx(&fmt_ctx)
        );
        // Check if the clause is about the same trait
        if clause.trait_id != trait_id {
            trace!("Not the same trait id");
            false
        } else {
            // Ignoring the regions for now
            let tgt_types = &generics.types;
            let tgt_const_generics = &generics.const_generics;

            let src_types = &clause.generics.types;
            let src_const_generics = &clause.generics.const_generics;

            // We simply check the equality between the arguments:
            // there are no universally quantified variables to unify.
            // TODO: normalize the trait clauses (we actually
            // need to check equality **modulo** equality clauses)
            // TODO: if we need to unify (later, when allowing universal
            // quantification over clause parameters), use types_utils::TySubst.
            let matched = src_types == tgt_types && src_const_generics == tgt_const_generics;
            trace!("Match successful: {}", matched);
            matched
        }
    }

    /// Find the trait instance fullfilling a trait obligation.
    /// TODO: having to do this is very annoying. Isn't there a better way?
    fn find_trait_clause_for_param(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs,
    ) -> TraitInstanceId {
        trace!(
            "Inside context of: {:?}\nSpan: {:?}",
            self.def_id,
            self.t_ctx.tcx.def_ident_span(self.def_id)
        );

        // Simply explore the trait clauses
        // Could not find a clause.
        // Check if we are in the registration process, otherwise report an error.
        // TODO: we might be registering a where clause.
        if self.registering_trait_clauses {
            TraitInstanceId::Unsolved(trait_id, generics.clone())
        } else {
            let fmt_ctx = self.into_fmt();
            let trait_ref = format!(
                "{}{}",
                fmt_ctx.format_object(trait_id),
                generics.fmt_with_ctx(&fmt_ctx)
            );
            let clauses: Vec<String> = Vec::new();

            if !self.t_ctx.continue_on_failure {
                let clauses = clauses.join("\n");
                unreachable!(
                    "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}\n- context: {:?}",
                    trait_ref, clauses, self.def_id
                );
            } else {
                // Return the UNKNOWN clause
                log::warn!(
                    "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}\n- context: {:?}",
                    trait_ref, clauses.join("\n"), self.def_id
                );
                TraitInstanceId::Unknown(format!(
                    "Could not find a clause for parameter: {} (available clauses: {}) (context: {:?})",
                    trait_ref,
                    clauses.join("; "),
                    self.def_id
                ))
            }
        }
    }
}

struct TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// The number of unsolved trait instances. This allows us to check whether we reached
    /// a fixed point or not (so that we don't enter infinite loops if we fail to solve
    /// some instances).
    pub unsolved_count: usize,
    /// The unsolved clauses.
    pub unsolved: Vec<(TraitDeclId::Id, GenericArgs)>,
    /// For error messages
    pub span: rustc_span::Span,
    /// The current context
    pub ctx: &'a mut BodyTransCtx<'tcx, 'ctx, 'ctx1>,
}

impl<'a, 'tcx, 'ctx, 'ctx1> MutTypeVisitor for TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// If we find an unsolved trait instance id, attempt to solve it
    fn visit_trait_instance_id(&mut self, id: &mut TraitInstanceId) {
        if let TraitInstanceId::Unsolved(trait_id, generics) = id {
            let solved_id = self.ctx.find_trait_clause_for_param(*trait_id, generics);

            if let TraitInstanceId::Unsolved(..) = solved_id {
                // Failure: increment the unsolved count
                self.unsolved_count += 1;
            } else {
                // Success: replace
                *id = solved_id;
            }
        } else {
            MutTypeVisitor::default_visit_trait_instance_id(self, id);
        }
    }
}

impl<'a, 'tcx, 'ctx, 'ctx1> SharedTypeVisitor for TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// If we find an unsolved trait instance id, save it
    fn visit_trait_instance_id(&mut self, id: &TraitInstanceId) {
        if let TraitInstanceId::Unsolved(trait_id, generics) = id {
            self.unsolved.push((*trait_id, generics.clone()))
        } else {
            SharedTypeVisitor::default_visit_trait_instance_id(self, id);
        }
    }
}

impl<'a, 'tcx, 'ctx, 'ctx1> TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// Auxiliary function
    fn visit(&mut self, solve: bool) {
        //
        // Explore the trait clauses map
        //

        // For now we clone the trait clauses map - we will make it more effcicient later
        let mut trait_clauses: Vec<(TraitInstanceId, NonLocalTraitClause)> = Vec::new();
        for (_, clause) in trait_clauses.iter_mut() {
            if solve {
                MutTypeVisitor::visit_trait_instance_id(self, &mut clause.clause_id);
                MutTypeVisitor::visit_generic_args(self, &mut clause.generics);
            } else {
                SharedTypeVisitor::visit_trait_instance_id(self, &clause.clause_id);
                SharedTypeVisitor::visit_generic_args(self, &clause.generics);
            }
        }

        // If we are solving: reconstruct the trait clauses map, and replace the one in the context
        if solve {
        }

        //
        // Also explore the other predicates
        // Remark: we could do this *after* we solved all the trait obligations
        // in the trait clauses map.

        // Types outlive predicates
        // TODO: annoying that we have to clone
        let mut types_outlive = self.ctx.types_outlive.clone();
        for x in &mut types_outlive {
            if solve {
                MutTypeVisitor::visit_type_outlives(self, x);
            } else {
                SharedTypeVisitor::visit_type_outlives(self, x);
            }
        }
        // Replace
        if solve {
            self.ctx.types_outlive = types_outlive;
        }

        // Trait type constraints predicates
        // TODO: annoying that we have to clone
        let mut trait_type_constraints = self.ctx.trait_type_constraints.clone();
        for x in &mut trait_type_constraints {
            if solve {
                MutTypeVisitor::visit_trait_type_constraint(self, x);
            } else {
                SharedTypeVisitor::visit_trait_type_constraint(self, x);
            }
        }
        // Replace
        if solve {
            self.ctx.trait_type_constraints = trait_type_constraints;
        }
    }

    /// Perform one pass of solving the trait obligations
    fn solve_one_pass(&mut self) {
        self.unsolved_count = 0;
        self.visit(true);
    }

    fn collect_unsolved(&mut self) {
        self.unsolved.clear();
        self.visit(false);
    }

    /// While there are unsolved trait obligations in the registered trait
    /// clauses, solve them (unless we get stuck).
    pub(crate) fn solve_repeat(&mut self) {
        self.solve_one_pass();

        let mut count = self.unsolved_count;
        let mut pass_id = 0;
        while count > 0 {
            log::trace!("Pass id: {}, unsolved count: {}", pass_id, count);
            self.solve_one_pass();
            if self.unsolved_count >= count {
                // We're stuck: report an error

                // Retraverse the context, collecting the unsolved clauses.
                self.collect_unsolved();

                let ctx = self.ctx.into_fmt();
                let _unsolved = self
                    .unsolved
                    .iter()
                    .map(|(trait_id, generics)| {
                        format!(
                            "{}{}",
                            ctx.format_object(*trait_id),
                            generics.fmt_with_ctx(&ctx)
                        )
                    })
                    .collect::<Vec<String>>()
                    .join("\n");
                return;
            } else {
                // We made progress: update the count
                count = self.unsolved_count;
                pass_id += 1;
            }
        }

        // We're done: check the where clauses which are not trait predicates
        self.collect_unsolved();
        assert!(self.unsolved.is_empty());
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Solve the unsolved trait obligations in the trait clauses (some clauses
    /// may refer to other clauses, meaning that we are not necessarily able
    /// to solve all the trait obligations when registering a clause, but might
    /// be able later).
    /// TODO: doing this in several passes is probably not necessary anymore
    pub(crate) fn solve_trait_obligations_in_trait_clauses(&mut self, span: rustc_span::Span) {
        let mut solver = TraitInstancesSolver {
            unsolved_count: 0,
            unsolved: Vec::new(),
            span,
            ctx: self,
        };

        solver.solve_repeat()
    }
}
