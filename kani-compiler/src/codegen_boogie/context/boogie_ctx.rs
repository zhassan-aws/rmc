// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::io::Write;

use crate::kani_queries::QueryDb;
use boogie_ast::boogie_program::{
    BinaryOp, BoogieProgram, Expr, Function, Literal, Parameter, Procedure, Stmt, Type,
};
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::traversal::reverse_postorder;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, Const as mirConst, ConstOperand, ConstValue,
    HasLocalDecls, Local, Operand, Place, ProjectionElem, Rvalue, Statement, StatementKind,
    SwitchTargets, Terminator, TerminatorKind,
};
use rustc_middle::span_bug;
use rustc_middle::ty::layout::{
    HasParamEnv, HasTyCtxt, LayoutError, LayoutOf, LayoutOfHelpers, TyAndLayout,
};
use rustc_middle::ty::{self, Instance, IntTy, Ty, TyCtxt, UintTy};
use rustc_span::Span;
use rustc_target::abi::{HasDataLayout, TargetDataLayout};
use strum::VariantNames;
use tracing::{debug, debug_span, trace};

use super::kani_intrinsic::{get_kani_intrinsic, KaniIntrinsic};

fn unsigned_less_than(width: usize) -> Function {
    Function::new(
        format!("$UnsignedLessThanBv{width}"),
        vec![
            Parameter::new("lhs".into(), Type::Bv(width)),
            Parameter::new("rhs".into(), Type::Bv(width)),
        ],
        Type::Bool,
        None,
        vec![String::from(":bvbuiltin \"bvult\"")],
    )
}

fn unsigned_add(width: usize) -> Function {
    Function::new(
        format!("$UnsignedAddBv{width}"),
        vec![
            Parameter::new("lhs".into(), Type::Bv(width)),
            Parameter::new("rhs".into(), Type::Bv(width)),
        ],
        Type::Bv(width),
        None,
        vec![String::from(":bvbuiltin \"bvadd\"")],
    )
}

/// A context that provides the main methods for translating MIR constructs to
/// Boogie and stores what has been codegen so far
pub struct BoogieCtx<'tcx> {
    /// the typing context
    pub tcx: TyCtxt<'tcx>,
    /// a snapshot of the query values. The queries shouldn't change at this point,
    /// so we just keep a copy.
    pub queries: QueryDb,
    /// the Boogie program
    program: BoogieProgram,
    /// Kani intrinsics
    pub intrinsics: Vec<String>,
}

/// A context for translating a function that holds the information needed
impl<'tcx> BoogieCtx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, queries: QueryDb) -> BoogieCtx {
        let mut program = BoogieProgram::new();

        // TODO: The current functions in the preamble should be added lazily instead
        Self::add_preamble(&mut program);

        BoogieCtx {
            tcx,
            queries,
            program,
            intrinsics: KaniIntrinsic::VARIANTS.iter().map(|s| (*s).into()).collect(),
        }
    }

    fn add_preamble(program: &mut BoogieProgram) {
        program.add_function(unsigned_less_than(64));
        program.add_function(unsigned_add(64));
    }

    /// Codegen a function into a Boogie procedure.
    /// Returns `None` if the function is a hook.
    pub fn codegen_function<'a>(&'a self, instance: Instance<'tcx>) -> Option<Procedure> {
        debug!(?instance, "boogie_codegen_function");
        if get_kani_intrinsic(self.tcx, instance).is_some() {
            debug!("skipping kani intrinsic `{instance}`");
            return None;
        }
        let mir = self.tcx.instance_mir(instance.def);
        let fcx = FunctionCtx::new(self, instance, mir);
        let mut decl = fcx.codegen_declare_variables();
        let body = fcx.codegen_body();
        decl.push(body);
        Some(Procedure::new(
            self.tcx.symbol_name(instance).name.to_string(),
            vec![],
            vec![],
            None,
            Stmt::Block { statements: decl },
        ))
    }

    pub fn add_procedure(&mut self, procedure: Procedure) {
        self.program.add_procedure(procedure);
    }

    /// Write the program to the given writer
    pub fn write<T: Write>(&self, writer: &mut T) -> std::io::Result<()> {
        self.program.write_to(writer)?;
        Ok(())
    }
}

pub struct FunctionCtx<'a, 'tcx> {
    bcx: &'a BoogieCtx<'tcx>,
    instance: Instance<'tcx>,
    mir: &'a Body<'tcx>,
}

impl<'a, 'tcx> FunctionCtx<'a, 'tcx> {
    pub fn new(
        bcx: &'a BoogieCtx<'tcx>,
        instance: Instance<'tcx>,
        mir: &'a Body<'tcx>,
    ) -> FunctionCtx<'a, 'tcx> {
        Self { bcx, instance, mir }
    }

    pub fn codegen_declare_variables(&self) -> Vec<Stmt> {
        let ldecls = self.mir.local_decls();
        let decls: Vec<Stmt> = ldecls
            .indices()
            .enumerate()
            .filter_map(|(_idx, lc)| {
                let typ = ldecls[lc].ty;
                if self.layout_of(typ).is_zst() {
                    return None;
                }
                debug!(?lc, ?typ, "codegen_declare_variables");
                let name = format!("{lc:?}");
                let boogie_type = self.codegen_type(typ);
                Some(Stmt::Decl { name, typ: boogie_type })
            })
            .collect();
        decls
    }

    fn codegen_type(&self, ty: Ty<'tcx>) -> Type {
        trace!(typ=?ty, "codegen_type");
        match ty.kind() {
            ty::Bool => Type::Bool,
            ty::Int(ity) => Type::Bv(ity.bit_width().unwrap_or(64).try_into().unwrap()),
            ty::Uint(uty) => Type::Bv(uty.bit_width().unwrap_or(64).try_into().unwrap()),
            ty::Array(elem_type, _len) => {
                Type::Array { element_type: Box::new(self.codegen_type(*elem_type)), len: 0 }
            }
            ty::Tuple(types) => {
                // Only handles first element of tuple for now
                self.codegen_type(types.iter().next().unwrap())
            }
            _ => todo!(),
        }
    }

    fn codegen_body(&self) -> Stmt {
        let mir = self.mir;
        let statements: Vec<Stmt> =
            reverse_postorder(mir).map(|(bb, bbd)| self.codegen_block(bb, bbd)).collect();
        Stmt::Block { statements }
    }

    fn codegen_block(&self, bb: BasicBlock, bbd: &BasicBlockData<'tcx>) -> Stmt {
        debug!(?bb, ?bbd, "codegen_block");
        let label = format!("{bb:?}");
        // the first statement should be labelled. if there are no statements, then the
        // terminator should be labelled.
        let statements = match bbd.statements.len() {
            0 => {
                let tcode = self.codegen_terminator(bbd.terminator());
                vec![Stmt::Label { label, statement: Box::new(tcode) }]
            }
            _ => {
                let mut statements: Vec<Stmt> = bbd
                    .statements
                    .iter()
                    .enumerate()
                    .map(|(index, stmt)| {
                        let s = self.codegen_statement(stmt);
                        if index == 0 {
                            Stmt::Label { label: label.clone(), statement: Box::new(s) }
                        } else {
                            s
                        }
                    })
                    .collect();

                let term = self.codegen_terminator(bbd.terminator());
                statements.push(term);
                statements
            }
        };
        Stmt::block(statements)
    }

    fn codegen_statement(&self, stmt: &Statement<'tcx>) -> Stmt {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                debug!(?place, ?rvalue, "codegen_statement");
                let place_name = format!("{:?}", place.local);
                if place_name.starts_with("nd__") || matches!(rvalue, Rvalue::Repeat(..)) {
                    Stmt::Havoc { name: place_name }
                } else {
                    let rv = self.codegen_rvalue(rvalue);
                    // assignment statement
                    let asgn = Stmt::Assignment { target: place_name, value: rv.1 };
                    // add it to other statements generated while creating the rvalue (if any)
                    add_statement(rv.0, asgn)
                }
            }
            StatementKind::FakeRead(..)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::Deinit(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Retag(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::Intrinsic(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => todo!(),
        }
    }

    /// Codegen an rvalue. Returns the expression for the rvalue and an optional
    /// statement for any possible checks instrumented for the rvalue expression
    fn codegen_rvalue(&self, rvalue: &Rvalue<'tcx>) -> (Option<Stmt>, Expr) {
        debug!(rvalue=?rvalue, "codegen_rvalue");
        match rvalue {
            Rvalue::Use(operand) => (None, self.codegen_operand(operand)),
            Rvalue::BinaryOp(binop, box (lhs, rhs)) => self.codegen_binary_op(binop, lhs, rhs),
            Rvalue::CheckedBinaryOp(binop, box (ref e1, ref e2)) => {
                // TODO: handle overflow check
                self.codegen_binary_op(binop, e1, e2)
            }
            _ => todo!(),
        }
    }

    fn codegen_binary_op(
        &self,
        binop: &BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
    ) -> (Option<Stmt>, Expr) {
        debug!(binop=?binop, "codegen_binary_op");
        let left = Box::new(self.codegen_operand(lhs));
        let right = Box::new(self.codegen_operand(rhs));
        let expr = match binop {
            BinOp::Eq => Expr::BinaryOp { op: BinaryOp::Eq, left, right },
            BinOp::AddUnchecked | BinOp::Add => {
                let left_type = self.operand_ty(lhs);
                if self.operand_ty(rhs) != left_type {
                    todo!("Addition of different types is not yet supported");
                } else {
                    let bv_func = match left_type.kind() {
                        ty::Int(it) => format!("$SignedAddBv{}", it.bit_width().unwrap_or(64)),
                        ty::Uint(it) => format!("$UnsignedAddBv{}", it.bit_width().unwrap_or(64)),
                        _ => todo!(),
                    };
                    Expr::function_call(bv_func, vec![*left, *right])
                }
            }
            BinOp::Lt => {
                let left_type = self.operand_ty(lhs);
                assert_eq!(left_type, self.operand_ty(rhs));
                let bv_func = match left_type.kind() {
                    ty::Int(it) => format!("$SignedLessThanBv{}", it.bit_width().unwrap_or(64)),
                    ty::Uint(it) => format!("$UnsignedLessThanBv{}", it.bit_width().unwrap_or(64)),
                    _ => todo!(),
                };
                Expr::function_call(bv_func, vec![*left, *right])
            }
            _ => todo!(),
        };
        (None, expr)
    }

    fn codegen_terminator(&self, term: &Terminator<'tcx>) -> Stmt {
        let _trace_span = debug_span!("CodegenTerminator", statement = ?term.kind).entered();
        debug!("handling terminator {:?}", term);
        match &term.kind {
            TerminatorKind::Call { func, args, destination, target, .. } => {
                self.codegen_funcall(func, args, destination, target, term.source_info.span)
            }
            TerminatorKind::Return => Stmt::Return,
            TerminatorKind::Goto { target } => Stmt::Goto { label: format!("{target:?}") },
            TerminatorKind::SwitchInt { discr, targets } => self.codegen_switch_int(discr, targets),
            TerminatorKind::Assert { .. } => Stmt::Block { statements: vec![] }, // do nothing for now
            _ => todo!(),
        }
    }

    fn codegen_funcall(
        &self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
        span: Span,
    ) -> Stmt {
        debug!(?func, ?args, ?destination, ?span, "codegen_funcall");
        let fargs = self.codegen_funcall_args(args);
        let funct = self.operand_ty(func);
        // TODO: Only Kani intrinsics are handled currently
        match &funct.kind() {
            ty::FnDef(defid, substs) => {
                let instance = Instance::expect_resolve(
                    self.bcx.tcx,
                    ty::ParamEnv::reveal_all(),
                    *defid,
                    substs,
                );

                if let Some(intrinsic) = get_kani_intrinsic(self.bcx.tcx, instance) {
                    return self.codegen_kani_intrinsic(
                        intrinsic,
                        instance,
                        fargs,
                        *destination,
                        *target,
                        Some(span),
                    );
                }
                todo!()
            }
            _ => todo!(),
        }
    }

    fn codegen_switch_int(&self, discr: &Operand<'tcx>, targets: &SwitchTargets) -> Stmt {
        debug!(discr=?discr, targets=?targets, "codegen_switch_int");
        let op = self.codegen_operand(discr);
        if targets.all_targets().len() == 2 {
            let then = targets.iter().next().unwrap();
            let right = match self.operand_ty(discr).kind() {
                ty::Bool => Literal::Bool(then.0 != 0),
                ty::Uint(_) => Literal::bv(128, then.0.into()),
                _ => unreachable!(),
            };
            // model as an if
            return Stmt::If {
                condition: Expr::BinaryOp {
                    op: BinaryOp::Eq,
                    left: Box::new(op),
                    right: Box::new(Expr::Literal(right)),
                },
                body: Box::new(Stmt::Goto { label: format!("{:?}", then.1) }),
                else_body: Some(Box::new(Stmt::Goto {
                    label: format!("{:?}", targets.otherwise()),
                })),
            };
        }
        todo!()
    }

    fn codegen_funcall_args(&self, args: &[Operand<'tcx>]) -> Vec<Expr> {
        debug!(?args, "codegen_funcall_args");
        args.iter()
            .filter_map(|o| {
                let ty = self.operand_ty(o);
                // TODO: handle non-primitive types
                if ty.is_primitive() {
                    return Some(self.codegen_operand(o));
                }
                // TODO: ignore non-primitive arguments for now (e.g. `msg`
                // argument of `kani::assert`)
                None
            })
            .collect()
    }

    fn codegen_operand(&self, o: &Operand<'tcx>) -> Expr {
        trace!(operand=?o, "codegen_operand");
        // A MIR operand is either a constant (literal or `const` declaration)
        // or a place (being moved or copied for this operation).
        // An "operand" in MIR is the argument to an "Rvalue" (and is also used
        // by some statements.)
        match o {
            Operand::Copy(place) | Operand::Move(place) => self.codegen_place(place),
            Operand::Constant(c) => self.codegen_constant(c),
        }
    }

    pub fn codegen_place(&self, place: &Place<'tcx>) -> Expr {
        debug!(place=?place, "codegen_place");
        debug!(place.local=?place.local, "codegen_place");
        debug!(place.projection=?place.projection, "codegen_place");
        let local = self.codegen_local(place.local);
        place.projection.iter().fold(local, |place, proj| {
            match proj {
                ProjectionElem::Index(i) => {
                    let index = self.codegen_local(i);
                    Expr::Index { base: Box::new(place), index: Box::new(index) }
                }
                _ => {
                    // TODO: handle
                    place
                }
            }
        })
    }

    fn codegen_local(&self, local: Local) -> Expr {
        // TODO: handle function definitions
        Expr::Symbol { name: format!("{local:?}") }
    }

    fn codegen_constant(&self, c: &ConstOperand<'tcx>) -> Expr {
        trace!(constant=?c, "codegen_constant");
        // TODO: monomorphize
        match c.const_ {
            mirConst::Val(val, ty) => self.codegen_constant_value(val, ty),
            _ => todo!(),
        }
    }

    fn codegen_constant_value(&self, val: ConstValue<'tcx>, ty: Ty<'tcx>) -> Expr {
        debug!(val=?val, "codegen_constant_value");
        match val {
            ConstValue::Scalar(s) => self.codegen_scalar(s, ty),
            _ => todo!(),
        }
    }

    fn codegen_scalar(&self, s: Scalar, ty: Ty<'tcx>) -> Expr {
        debug!(kind=?ty.kind(), "codegen_scalar");
        match (s, ty.kind()) {
            (Scalar::Int(_), ty::Bool) => Expr::Literal(Literal::Bool(s.to_bool().unwrap())),
            (Scalar::Int(_), ty::Int(it)) => match it {
                IntTy::I8 => Expr::Literal(Literal::Int(s.to_i8().unwrap().into())),
                IntTy::I16 => Expr::Literal(Literal::Int(s.to_i16().unwrap().into())),
                IntTy::I32 => Expr::Literal(Literal::Int(s.to_i32().unwrap().into())),
                IntTy::I64 => Expr::Literal(Literal::Int(s.to_i64().unwrap().into())),
                IntTy::I128 => Expr::Literal(Literal::Int(s.to_i128().unwrap().into())),
                IntTy::Isize => {
                    // TODO: get target width
                    Expr::Literal(Literal::Int(s.to_target_isize(self).unwrap().into()))
                }
            },
            (Scalar::Int(_), ty::Uint(it)) => match it {
                UintTy::U8 => Expr::Literal(Literal::bv(8, s.to_u8().unwrap().into())),
                UintTy::U16 => Expr::Literal(Literal::bv(16, s.to_u16().unwrap().into())),
                UintTy::U32 => Expr::Literal(Literal::bv(32, s.to_u32().unwrap().into())),
                UintTy::U64 => Expr::Literal(Literal::bv(64, s.to_u64().unwrap().into())),
                UintTy::U128 => Expr::Literal(Literal::bv(128, s.to_u128().unwrap().into())),
                UintTy::Usize => {
                    // TODO: get target width
                    Expr::Literal(Literal::bv(64, s.to_target_usize(self).unwrap().into()))
                }
            },
            _ => todo!(),
        }
    }

    fn operand_ty(&self, o: &Operand<'tcx>) -> Ty<'tcx> {
        // TODO: monomorphize
        o.ty(self.mir.local_decls(), self.bcx.tcx)
    }
}

impl<'a, 'tcx> LayoutOfHelpers<'tcx> for FunctionCtx<'a, 'tcx> {
    type LayoutOfResult = TyAndLayout<'tcx>;

    fn handle_layout_err(&self, err: LayoutError<'tcx>, span: Span, ty: Ty<'tcx>) -> ! {
        span_bug!(span, "failed to get layout for `{}`: {}", ty, err)
    }
}

impl<'a, 'tcx> HasParamEnv<'tcx> for FunctionCtx<'a, 'tcx> {
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        ty::ParamEnv::reveal_all()
    }
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for FunctionCtx<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.bcx.tcx
    }
}

impl<'a, 'tcx> HasDataLayout for FunctionCtx<'a, 'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.bcx.tcx.data_layout()
    }
}

/// Create a new statement that includes `s1` (if non-empty) and `s2`
fn add_statement(s1: Option<Stmt>, s2: Stmt) -> Stmt {
    match s1 {
        Some(s1) => match s1 {
            Stmt::Block { mut statements } => {
                statements.push(s2);
                Stmt::Block { statements }
            }
            _ => Stmt::Block { statements: vec![s1, s2] },
        },
        None => s2,
    }
}
