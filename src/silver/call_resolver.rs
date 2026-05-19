//! Call Resolution Pass
//!
//! This module is responsible for resolving the concrete semantic types of all invocations
//! within a Silver program.
//!
//! Because Silver's grammar features syntactic ambiguities, the parser creates generic
//! call nodes for all function-like invocations (e.g., `f(x)`). Furthermore, it greedily
//! parses all assignment-call right-hand sides (e.g., `y := f(x)`) as [`AssignRhs::Call`].
//!
//! The `CallResolver` performs a mutable, bottom-up traversal of the AST, querying
//! the pre-computed [`Globals`] interner to definitively categorize these syntactic constructs
//! into their correct semantic representations.
//!
//! # Responsibilities
//!
//! 1. **Expression call resolution**: Evaluates generic expression call nodes and tags them.
//!
//! 2. **Macro Desugaring**: Evaluates bare [`ExpKind::Ident`] nodes. If the identifier corresponds
//!    to a parameterless global macro, it physically replaces the identifier node with a
//!    zero-argument [`ExpKind::App`] node tagged as a macro.
//!
//! 3. **Statement vs. expression lowering**: Evaluates [`AssignRhs::Call`] nodes generated
//!    by the parser. If the target is a genuine imperative `Method`, it remains a statement-level
//!    assignment. If the target is a function, predicate, or macro, the assignment is "demoted"
//!    down into an [`AssignRhs::Exp`] so it can be evaluated as a standard mathematical expression.

use crate::silver::{
    AssignRhs, Call, Exp, ExpCallKind, ExpKind, Globals, StmtCallKind,
    globals::GlobalKind,
    interner::Interner,
    walk::{AstWalkable, AstWalkerMut},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallResolutionError {
    UnresolvedCallable(String),
    StatementCallInExpression(String, GlobalKind),
    NotCallable(String, GlobalKind),
}

impl std::fmt::Display for CallResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CallResolutionError::UnresolvedCallable(name) => {
                write!(f, "cannot find callable `{name}`")
            }
            CallResolutionError::StatementCallInExpression(name, kind) => {
                write!(f, "{kind} `{name}` cannot be called inside an expression")
            }
            CallResolutionError::NotCallable(name, kind) => {
                write!(f, "cannot call `{name}` because it is a {kind}")
            }
        }
    }
}

impl std::error::Error for CallResolutionError {}

struct CallResolver<'i, 'g> {
    interner: &'i Interner,
    globals: &'g Globals,
    errors: Vec<CallResolutionError>,
}

impl<'i, 'g> CallResolver<'i, 'g> {
    fn new(interner: &'i Interner, globals: &'g Globals) -> Self {
        Self {
            interner,
            globals,
            errors: Vec::new(),
        }
    }
}

impl<'i, 'g> AstWalkerMut<'_> for CallResolver<'i, 'g> {
    fn walk_mut_assign_rhs(&mut self, rhs: &'_ mut AssignRhs) {
        // Intercept bare identifiers being used as statement right-hand sides.
        if let AssignRhs::Exp(exp) = rhs
            && let ExpKind::Ident(name) = &*exp.kind
            && Some(GlobalKind::StmtMacro) == self.globals.resolve(name.id()).map(|sym| sym.kind())
        {
            *rhs = AssignRhs::Call(crate::silver::Call {
                kind: None, // Will be correctly tagged below
                name: name.clone(),
                args: Vec::new(),
            });
        }

        if let AssignRhs::Call(call) = rhs {
            let id = call.name.id();
            let call_tgt_name = || self.interner.resolve(&id).to_string();

            if let Some(sym) = self.globals.resolve(id) {
                match sym.kind() {
                    // STATEMENT CONTEXT
                    GlobalKind::Method => {
                        call.kind = Some(StmtCallKind::Method);
                        for arg in &mut call.args {
                            arg.walk_mut(self);
                        }
                    }
                    GlobalKind::StmtMacro => {
                        call.kind = Some(StmtCallKind::Macro);
                        for arg in &mut call.args {
                            arg.walk_mut(self);
                        }
                    }

                    // EXPRESSION CONTEXT
                    // Let `walk_mut_exp_call` handle specific kind resolution and arguments!
                    GlobalKind::Function
                    | GlobalKind::Predicate
                    | GlobalKind::ExpMacro
                    | GlobalKind::AdtConstructor => {
                        let mut new_call = crate::silver::Call {
                            kind: None,
                            name: call.name.clone(),
                            args: std::mem::take(&mut call.args),
                        };
                        self.walk_mut_exp_call(&mut new_call);
                        *rhs = AssignRhs::Exp(Exp::unknown(ExpKind::Call(new_call)));
                    }

                    // INVALID CALL TARGETS
                    actual_kind => {
                        for arg in &mut call.args {
                            arg.walk_mut(self);
                        }
                        self.errors.push(CallResolutionError::NotCallable(
                            call_tgt_name(),
                            actual_kind,
                        ));
                    }
                }
            } else {
                // UNRESOLVED IDENTIFIER
                for arg in &mut call.args {
                    arg.walk_mut(self);
                }
                self.errors
                    .push(CallResolutionError::UnresolvedCallable(call_tgt_name()));
            }
        } else {
            rhs.walk_mut_children(self);
        }
    }

    fn walk_mut_exp_call(&mut self, call: &'_ mut Call<ExpCallKind>) {
        for arg in &mut call.args {
            arg.walk_mut(self);
        }

        let id = call.name.id();
        let call_tgt_name = || self.interner.resolve(&id).to_string();

        if let Some(sym) = self.globals.resolve(id) {
            match sym.kind() {
                // EXPRESSION CONTEXT: Valid callable targets
                GlobalKind::Function => call.kind = Some(ExpCallKind::Function),
                GlobalKind::Predicate => call.kind = Some(ExpCallKind::Predicate),
                GlobalKind::ExpMacro => call.kind = Some(ExpCallKind::Macro),
                GlobalKind::AdtConstructor => call.kind = Some(ExpCallKind::AdtConstructor),

                // INVALID: Trying to use a Statement inside an Expression!
                kind @ GlobalKind::Method | kind @ GlobalKind::StmtMacro => {
                    self.errors
                        .push(CallResolutionError::StatementCallInExpression(
                            call_tgt_name(),
                            kind,
                        ));
                }

                // INVALID: Targets that cannot be called at all (Fields, Domains, etc.)
                actual_kind => {
                    self.errors.push(CallResolutionError::NotCallable(
                        call_tgt_name(),
                        actual_kind,
                    ));
                }
            }
        } else {
            // UNRESOLVED IDENTIFIER
            self.errors
                .push(CallResolutionError::UnresolvedCallable(call_tgt_name()));
        }
    }

    fn walk_mut_exp_kind(&mut self, exp: &'_ mut ExpKind) {
        exp.walk_mut_children(self);

        if let ExpKind::Ident(name) = exp {
            let id = name.id();
            // ONLY desugar Expression macros! Statement macros without args
            // should not be desugared into Exp nodes!

            if let Some(sym) = self.globals.resolve(id)
                && sym.kind() == GlobalKind::ExpMacro
            {
                *exp = ExpKind::Call(crate::silver::Call {
                    kind: Some(ExpCallKind::Macro),
                    name: name.clone(),
                    args: Vec::new(),
                });
            }
        }
    }
}
