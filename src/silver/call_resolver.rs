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
    AssignRhs, Call, ExpCallKind, ExpKind, Globals, StmtCallKind,
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
        if let AssignRhs::Call(call) = rhs {
            for arg in &mut call.args {
                arg.walk_mut(self);
            }

            let id = call.name.id();

            let mut demote_to_exp = |exp_kind: ExpCallKind| {
                AssignRhs::Exp(Box::new(ExpKind::Call(Call {
                    kind: Some(exp_kind),
                    name: call.name.clone(),
                    args: std::mem::take(&mut call.args),
                })))
            };

            let call_tgt_name = || self.interner.resolve(&id).to_string();

            // Updated to use the new Globals API: lookup -> kind
            match self.globals.lookup(id).map(|mid| self.globals.kind(mid)) {
                // STATEMENT CONTEXT
                Some(GlobalKind::Method) => call.kind = Some(StmtCallKind::Method),
                Some(GlobalKind::StmtMacro) => call.kind = Some(StmtCallKind::Macro),

                // EXPRESSION CONTEXT
                Some(GlobalKind::Function) => *rhs = demote_to_exp(ExpCallKind::Function),
                Some(GlobalKind::Predicate) => *rhs = demote_to_exp(ExpCallKind::Predicate),
                Some(GlobalKind::ExpMacro) => *rhs = demote_to_exp(ExpCallKind::Macro),
                Some(GlobalKind::AdtConstructor) => {
                    *rhs = demote_to_exp(ExpCallKind::AdtConstructor)
                }

                // INVALID CALL TARGETS
                Some(actual_kind) => {
                    self.errors.push(CallResolutionError::NotCallable(
                        call_tgt_name(),
                        actual_kind,
                    ));
                }
                None => {
                    self.errors
                        .push(CallResolutionError::UnresolvedCallable(call_tgt_name()));
                }
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

        // Updated to use the new Globals API: lookup -> kind
        match self.globals.lookup(id).map(|mid| self.globals.kind(mid)) {
            // EXPRESSION CONTEXT: Valid callable targets
            Some(GlobalKind::Function) => call.kind = Some(ExpCallKind::Function),
            Some(GlobalKind::Predicate) => call.kind = Some(ExpCallKind::Predicate),
            Some(GlobalKind::ExpMacro) => call.kind = Some(ExpCallKind::Macro),
            Some(GlobalKind::AdtConstructor) => call.kind = Some(ExpCallKind::AdtConstructor),

            // INVALID: Trying to use a Statement inside an Expression!
            Some(kind @ GlobalKind::Method) | Some(kind @ GlobalKind::StmtMacro) => {
                self.errors
                    .push(CallResolutionError::StatementCallInExpression(
                        call_tgt_name(),
                        kind,
                    ));
            }

            // INVALID: Targets that cannot be called at all (Fields, Domains, etc.)
            Some(actual_kind) => {
                self.errors.push(CallResolutionError::NotCallable(
                    call_tgt_name(),
                    actual_kind,
                ));
            }

            // INVALID: Unknown identifier
            None => {
                self.errors
                    .push(CallResolutionError::UnresolvedCallable(call_tgt_name()));
            }
        }
    }

    fn walk_mut_exp_kind(&mut self, exp: &'_ mut ExpKind) {
        exp.walk_mut_children(self);

        if let ExpKind::Ident(name) = exp {
            let id = name.id();
            // ONLY desugar Expression macros! Statement macros without args
            // should not be desugared into Exp nodes!
            // Updated to use the new Globals API: lookup -> kind
            if let Some(GlobalKind::ExpMacro) =
                self.globals.lookup(id).map(|mid| self.globals.kind(mid))
            {
                *exp = ExpKind::Call(Call {
                    kind: Some(ExpCallKind::Macro),
                    name: name.clone(),
                    args: Vec::new(),
                });
            }
        }
    }
}
