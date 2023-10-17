// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A module that defines the AST of a Boogie program and provides methods for
//! creating nodes of the AST.

pub mod writer;

use num_bigint::BigInt;
use std::string::ToString;

struct TypeDeclaration {}
struct ConstDeclaration {}
struct VarDeclaration {}
struct Axiom {}

pub struct DataTypeConstructor {
    name: String,
    parameters: Vec<Parameter>,
}

impl DataTypeConstructor {
    pub fn new(name: String, parameters: Vec<Parameter>) -> Self {
        Self { name, parameters }
    }
}

pub struct DataTypeDeclaration {
    name: String,
    type_parameters: Vec<String>,
    constructors: Vec<DataTypeConstructor>,
}

impl DataTypeDeclaration {
    pub fn new(
        name: String,
        type_parameters: Vec<String>,
        constructors: Vec<DataTypeConstructor>,
    ) -> Self {
        Self { name, type_parameters, constructors }
    }
}

/// Boogie types
pub enum Type {
    /// Boolean
    Bool,

    /// Bit-vector of a given width, e.g. `bv32`
    Bv(usize),

    /// Unbounded integer
    Int,

    /// Map type, e.g. `[int]bool`
    Map { key: Box<Type>, value: Box<Type> },

    /// Type parameter
    Parameter { name: String },

    /// Array type
    Array { element_type: Box<Type>, len: usize },

    /// DataType
    DataType { name: String, type_arguments: Vec<Type> },
}

impl Type {
    pub fn bv(width: usize) -> Self {
        Self::Bv(width)
    }

    pub fn parameter(name: String) -> Self {
        Self::Parameter { name }
    }

    pub fn array(element_type: Box<Type>, len: usize) -> Self {
        Self::Array { element_type, len }
    }

    pub fn datatype(name: String, type_arguments: Vec<Type>) -> Self {
        Self::DataType { name, type_arguments }
    }

    pub fn map(key: Type, value: Type) -> Self {
        Self::Map { key: Box::new(key), value: Box::new(value) }
    }
}

/// Function and procedure parameters
pub struct Parameter {
    name: String,
    typ: Type,
}

impl Parameter {
    pub fn new(name: String, typ: Type) -> Self {
        Self { name, typ }
    }
}

/// Literal types
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    /// Boolean values: `true`/`false`
    Bool(bool),

    /// Bit-vector values, e.g. `5bv8`
    Bv { width: usize, value: BigInt },

    /// Unbounded integer values, e.g. `1000` or `-456789`
    Int(BigInt),
}

impl Literal {
    pub fn bv(width: usize, value: BigInt) -> Self {
        Self::Bv { width, value }
    }
}

/// Unary operators
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    /// Logical negation
    Not,

    /// Arithmetic negative
    Neg,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    /// Logical AND
    And,

    /// Logical OR
    Or,

    /// Equality
    Eq,

    /// Inequality
    Neq,

    /// Less than
    Lt,

    /// Less than or equal
    Lte,

    /// Greater than
    Gt,

    /// Greater than or equal
    Gte,

    /// Addition
    Add,

    /// Subtraction
    Sub,

    /// Multiplication
    Mul,

    /// Division
    Div,

    /// Modulo
    Mod,
}

/// Expr types
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// Literal (constant)
    Literal(Literal),

    /// Variable
    Symbol { name: String },

    /// Unary operation
    UnaryOp { op: UnaryOp, operand: Box<Expr> },

    /// Binary operation
    BinaryOp { op: BinaryOp, left: Box<Expr>, right: Box<Expr> },

    /// Function call
    FunctionCall { symbol: String, arguments: Vec<Expr> },

    /// Index operation
    Index { base: Box<Expr>, index: Box<Expr> },

    /// Field operator for datatypes
    Field { base: Box<Expr>, field: String },
}

impl Expr {
    pub fn function_call(symbol: String, arguments: Vec<Expr>) -> Self {
        Expr::FunctionCall { symbol, arguments }
    }
}

impl ToString for Expr {
    fn to_string(&self) -> String {
        let mut buf = Vec::new();
        let mut writer = writer::Writer::new(&mut buf);
        self.write_to(&mut writer).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

/// Statement types
pub enum Stmt {
    /// Assignment statement: `target := value;`
    Assignment { target: String, value: Expr },

    /// Assert statement: `assert condition;`
    Assert { condition: Expr },

    /// Assume statement: `assume condition;`
    Assume { condition: Expr },

    /// Statement block: `{ statements }`
    Block { statements: Vec<Stmt> },

    /// Break statement: `break;`
    /// A `break` in boogie can take a label, but this is probably not needed
    Break,

    /// Procedure call: `symbol(arguments);`
    Call { symbol: String, arguments: Vec<Expr> },

    /// Declaration statement: `var name: type;`
    Decl { name: String, typ: Type },

    /// Havoc statement: `havoc x;`
    Havoc { name: String },

    /// If statement: `if (condition) { body } else { else_body }`
    If { condition: Expr, body: Box<Stmt>, else_body: Option<Box<Stmt>> },

    /// Goto statement: `goto label;`
    Goto { label: String },

    /// Label statement: `label:`
    Label { label: String, statement: Box<Stmt> },

    /// `;`
    Null,

    /// Return statement: `return;`
    Return,

    /// While statement: `while (condition) { body }`
    While { condition: Expr, body: Box<Stmt> },
}

impl Stmt {
    pub fn block(mut statements: Vec<Stmt>) -> Stmt {
        // avoid creating a block if there is a single statement
        if statements.len() == 1 {
            return statements.remove(0);
        }
        Stmt::Block { statements }
    }

    pub fn decl(name: String, typ: Type) -> Stmt {
        Stmt::Decl { name, typ }
    }
}

/// Contract specification
pub struct Contract {
    /// Pre-conditions
    requires: Vec<Expr>,
    /// Post-conditions
    ensures: Vec<Expr>,
    /// Modifies clauses
    // TODO: should be symbols and not expressions
    modifies: Vec<Expr>,
}

/// Procedure definition
/// A procedure is a function that has a contract specification and that can
/// have side effects
pub struct Procedure {
    name: String,
    parameters: Vec<Parameter>,
    return_parameters: Vec<(String, Type)>,
    contract: Option<Contract>,
    body: Stmt,
}

impl Procedure {
    pub fn new(
        name: String,
        parameters: Vec<Parameter>,
        return_parameters: Vec<(String, Type)>,
        contract: Option<Contract>,
        body: Stmt,
    ) -> Self {
        Procedure { name, parameters, return_parameters, contract, body }
    }
}

/// Function definition
/// A function in Boogie is a mathematical function (deterministic, has no side
/// effects, and whose body is an expression)
pub struct Function {
    name: String,
    parameters: Vec<Parameter>,
    return_type: Type,
    body: Option<Expr>,
    attributes: Vec<String>,
}

impl Function {
    pub fn new(
        name: String,
        parameters: Vec<Parameter>,
        return_type: Type,
        body: Option<Expr>,
        attributes: Vec<String>,
    ) -> Self {
        Function { name, parameters, return_type, body, attributes }
    }
}

/// A boogie program
pub struct BoogieProgram {
    type_declarations: Vec<TypeDeclaration>,
    const_declarations: Vec<ConstDeclaration>,
    var_declarations: Vec<VarDeclaration>,
    axioms: Vec<Axiom>,
    datatypes: Vec<DataTypeDeclaration>,
    functions: Vec<Function>,
    procedures: Vec<Procedure>,
}

impl BoogieProgram {
    pub fn new() -> Self {
        BoogieProgram {
            type_declarations: Vec::new(),
            const_declarations: Vec::new(),
            var_declarations: Vec::new(),
            axioms: Vec::new(),
            datatypes: Vec::new(),
            functions: Vec::new(),
            procedures: Vec::new(),
        }
    }

    pub fn add_procedure(&mut self, procedure: Procedure) {
        self.procedures.push(procedure);
    }

    pub fn add_function(&mut self, function: Function) {
        self.functions.push(function);
    }

    pub fn add_datatype(&mut self, datatype: DataTypeDeclaration) {
        self.datatypes.push(datatype);
    }
}
