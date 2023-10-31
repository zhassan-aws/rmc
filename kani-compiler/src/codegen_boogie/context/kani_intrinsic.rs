// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module is for handling Kani intrinsics, i.e. items whose implementation
//! is defined in the Kani compiler. These items are defined in the `kani`
//! library and are annotated with a `rustc_diagnostic_item`.

use boogie_ast::boogie_program::{Expr, Stmt};
use rustc_middle::mir::{BasicBlock, Operand, Place};
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_span::Span;
use std::str::FromStr;
use strum::VariantNames;
use strum_macros::{EnumString, EnumVariantNames};
use tracing::debug;

use super::boogie_ctx::FunctionCtx;

// TODO: move this enum up to `kani_middle`
#[derive(Debug, Clone, PartialEq, Eq, EnumString, EnumVariantNames)]
pub enum KaniIntrinsic {
    /// Kani assert statement (`kani::assert`)
    KaniAssert,

    /// Kani assume statement (`kani::assume`)
    KaniAssume,

    /// Kani symbolic variable (`kani::any`)
    KaniAnyRaw,

    /// Kani unbounded array (`kani::array::any`)
    KaniAnyArray,

    KaniAnyArraySet,

    KaniAnyArrayGet,

    KaniAnyArrayLen,

    KaniAnyArrayIndex,

    KaniAnyArrayIndexMut,
}

/// If provided function is a Kani intrinsic (e.g. assert, assume, cover),
/// returns it
// TODO: move this function up to `kani_middle` along with the enum
pub fn get_kani_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Option<KaniIntrinsic> {
    debug!(?instance.def);
    for intrinsic in KaniIntrinsic::VARIANTS {
        let attr_sym = rustc_span::symbol::Symbol::intern(intrinsic);
        if let Some(attr_id) = tcx.all_diagnostic_items(()).name_to_id.get(&attr_sym) {
            if instance.def.def_id() == *attr_id {
                debug!("matched: {:?} {:?}", attr_id, attr_sym);
                return Some(KaniIntrinsic::from_str(intrinsic).unwrap());
            }
        }
    }
    None
}

impl<'a, 'tcx> FunctionCtx<'a, 'tcx> {
    pub fn codegen_kani_intrinsic(
        &mut self,
        intrinsic: KaniIntrinsic,
        instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Option<Span>,
    ) -> Stmt {
        match intrinsic {
            KaniIntrinsic::KaniAssert => {
                self.codegen_kani_assert(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAssume => {
                self.codegen_kani_assume(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyRaw => {
                self.codegen_kani_any_raw(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArray => {
                self.codegen_kani_any_array(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArraySet => {
                self.codegen_kani_any_array_set(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayGet => {
                self.codegen_kani_any_array_get(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayLen => {
                self.codegen_kani_any_array_len(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayIndex => {
                self.codegen_kani_any_array_index(instance, args, assign_to, target, span)
            }
            KaniIntrinsic::KaniAnyArrayIndexMut => {
                self.codegen_kani_any_array_index_mut(instance, args, assign_to, target, span)
            }
        }
    }

    pub fn codegen_kani_assert(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 2);
        // TODO: ignore the `'static str` argument for now
        let cond = self.codegen_operand(&args[0]);
        // TODO: handle message
        // TODO: handle location

        Stmt::Block {
            statements: vec![
                Stmt::Assert { condition: cond },
                // TODO: handle target
            ],
        }
    }

    pub fn codegen_kani_assume(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 1);
        let cond = self.codegen_operand(&args[0]);
        // TODO: handle location

        Stmt::Block {
            statements: vec![
                Stmt::Assume { condition: cond },
                // TODO: handle target
            ],
        }
    }

    pub fn codegen_kani_any_raw(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert!(args.is_empty());

        let place = self.codegen_place(&assign_to);

        let symbol = if let Expr::Symbol { name } = place {
            name
        } else {
            panic!("expecting place to be a symbol and not {place:?}.")
        };

        Stmt::Block {
            statements: vec![
                Stmt::Havoc { name: symbol },
                Stmt::Goto { label: format!("{:?}", target.unwrap()) },
            ],
        }
    }

    pub fn codegen_kani_any_array(
        &self,
        instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Option<Span>,
    ) -> Stmt {
        assert!(args.is_empty());

        self.codegen_kani_any_raw(instance, args, assign_to, target, span)
    }

    pub fn codegen_kani_any_array_set(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        _assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 3);
        debug!(?args, "codegen_kani_any_array_set");

        let mut_self_ref = &args[0];
        let Operand::Move(place) = mut_self_ref else {
            panic!("expecting first argument to be `Operand::Move`.");
        };
        let Some(expr) = self.ref_to_expr.get(place) else {
            panic!("expecting first argument to be a reference to an array.");
        };
        let map = Expr::Field { base: Box::new(expr.clone()), field: String::from("data") };

        let index = self.codegen_operand(&args[1]);

        // TODO: change `Stmt::Assignment` to be in terms of a symbol not a
        // string to avoid the hacky code below
        let index_expr = Expr::Index { base: Box::new(map), index: Box::new(index) };
        //let Expr::Symbol { name } = expr else { panic!("expecting expression to be a symbol") };
        //let Expr::Literal(literal) = index else { panic!("expecting index to be a literal") };
        //let Literal::
        //let index_oper = format!("{name}[{index}]");"
        let mut buf = Vec::new();
        let mut writer = boogie_ast::boogie_program::writer::Writer::new(&mut buf);
        index_expr.write_to(&mut writer).unwrap();
        let index_str = String::from_utf8(buf).unwrap();
        let value = self.codegen_operand(&args[2]);

        Stmt::Assignment { target: index_str, value }
    }

    pub fn codegen_kani_any_array_get(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 2);
        debug!(?args, "codegen_kani_any_array_get");
        debug!(?self.ref_to_expr);

        let self_ref = &args[0];
        let Operand::Move(place) = self_ref else {
            panic!("expecting first argument to be `Operand::Move`.");
        };
        let Some(expr) = self.ref_to_expr.get(place) else {
            panic!("expecting first argument to be a reference to an array.");
        };
        let map = Expr::Field { base: Box::new(expr.clone()), field: String::from("data") };

        let index = self.codegen_operand(&args[1]);
        let index_expr = Expr::Index { base: Box::new(map), index: Box::new(index) };

        let place = self.codegen_place(&assign_to);

        let Expr::Symbol { name } = place else { panic!("expecting place to be a symbol") };

        Stmt::Assignment { target: name, value: index_expr }
    }

    pub fn codegen_kani_any_array_len(
        &self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 1);
        debug!(?args, "codegen_kani_any_array_len");
        debug!(?self.ref_to_expr);

        let self_ref = &args[0];
        let expr = self
            .operand_to_expr(self_ref)
            .expect("expecting operand to be a ref to an existing expression");
        let len = Expr::Field { base: Box::new(expr.clone()), field: String::from("len") };

        let place = self.codegen_place(&assign_to);

        let Expr::Symbol { name } = place else { panic!("expecting place to be a symbol") };

        Stmt::Assignment { target: name, value: len }
    }

    pub fn codegen_kani_any_array_index(
        &self,
        instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Option<Span>,
    ) -> Stmt {
        self.codegen_kani_any_array_get(instance, args, assign_to, target, span)
    }

    pub fn codegen_kani_any_array_index_mut(
        &mut self,
        _instance: Instance<'tcx>,
        args: &[Operand<'tcx>],
        assign_to: Place<'tcx>,
        _target: Option<BasicBlock>,
        _span: Option<Span>,
    ) -> Stmt {
        assert_eq!(args.len(), 2);
        debug!(?args, "codegen_kani_any_array_index_mut");

        let mut_self_ref = &args[0];
        let expr = self
            .operand_to_expr(mut_self_ref)
            .expect("expecting operand to be a ref to an existing expression");
        let map = Expr::Field { base: Box::new(expr.clone()), field: String::from("data") };

        let index = self.codegen_operand(&args[1]);

        // TODO: change `Stmt::Assignment` to be in terms of a symbol not a
        // string to avoid the hacky code below
        let index_expr = Expr::Index { base: Box::new(map), index: Box::new(index) };
        self.ref_to_expr.insert(assign_to, index_expr);
        Stmt::Null
    }

    fn operand_to_expr(&self, operand: &Operand<'tcx>) -> Option<&Expr> {
        let Operand::Move(place) = operand else {
            return None;
        };
        self.ref_to_expr.get(place)
    }
}
