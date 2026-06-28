//! Disambiguation Pass
//!
//! Resolves syntactic ambiguities in the parsed Silver AST against the
//! pre-computed [`Globals`].
//!
//! The Silver grammar leaves several constructs ambiguous on the way out of
//! the parser; this pass classifies them by looking up the names they
//! reference:
//!
//! * Generic call nodes `f(x)` get tagged with the callee's kind
//!   (function, predicate, method, macro, ADT constructor).
//! * `AssignRhs::Call` is demoted to `AssignRhs::Exp` when the target is
//!   not actually a statement-shaped callee (function/predicate/macro/…).
//! * Bare `Ident` nodes get desugared into zero-argument macro calls
//!   when the identifier resolves to an expression macro.
//! * Field accesses `e.f` are validated against the globals table — `f`
//!   must resolve to a Viper field. (ADT-destructor recognition is
//!   deferred until the globals collector tracks destructor names.)
//!
//! All in-place rewrites happen under `walk_mut_*`; errors are collected
//! and reported in bulk.

use crate::viper::{
    AssignRhs, Call, Exp, ExpCallKind, ExpKind, Globals, Ident, StmtCallKind,
    globals::GlobalKind,
    interner::Interner,
    parsed::ast::InferenceType,
    walk::{AstWalkable, AstWalkerMut},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisambiguationError {
    UnresolvedCallable(String),
    StatementCallInExpression(String, GlobalKind),
    NotCallable(String, GlobalKind),
    UnknownField(String),
    NotAField(String, GlobalKind),
}

impl std::fmt::Display for DisambiguationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DisambiguationError::UnresolvedCallable(name) => {
                write!(f, "cannot find callable `{name}`")
            }
            DisambiguationError::StatementCallInExpression(name, kind) => {
                write!(f, "{kind} `{name}` cannot be called inside an expression")
            }
            DisambiguationError::NotCallable(name, kind) => {
                write!(f, "cannot call `{name}` because it is a {kind}")
            }
            DisambiguationError::UnknownField(name) => {
                write!(f, "unknown field `{name}`")
            }
            DisambiguationError::NotAField(name, kind) => {
                write!(f, "`{name}` is a {kind}, not a field")
            }
        }
    }
}

impl std::error::Error for DisambiguationError {}

struct Disambiguator<'i, 'g> {
    interner: &'i Interner,
    globals: &'g Globals,
    errors: Vec<DisambiguationError>,
}

impl<'i, 'g> Disambiguator<'i, 'g> {
    fn new(interner: &'i Interner, globals: &'g Globals) -> Self {
        Self {
            interner,
            globals,
            errors: Vec::new(),
        }
    }
}

impl<'i, 'g> AstWalkerMut<'_> for Disambiguator<'i, 'g> {
    fn walk_mut_assign_rhs(&mut self, rhs: &'_ mut AssignRhs) {
        // Intercept bare identifiers being used as statement right-hand sides.
        if let AssignRhs::Exp(exp) = rhs
            && let ExpKind::Ident(name) = &*exp.kind
            && Some(GlobalKind::StmtMacro) == self.globals.resolve(name.id()).map(|sym| sym.kind())
        {
            *rhs = AssignRhs::Call(crate::viper::Call {
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
                    | GlobalKind::DomainFunction
                    | GlobalKind::Predicate
                    | GlobalKind::ExpMacro
                    | GlobalKind::AdtConstructor => {
                        let mut new_call = crate::viper::Call {
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
                        self.errors.push(DisambiguationError::NotCallable(
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
                    .push(DisambiguationError::UnresolvedCallable(call_tgt_name()));
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
                GlobalKind::DomainFunction => call.kind = Some(ExpCallKind::DomainFunction),
                GlobalKind::Predicate => call.kind = Some(ExpCallKind::Predicate),
                GlobalKind::ExpMacro => call.kind = Some(ExpCallKind::Macro),
                GlobalKind::AdtConstructor => call.kind = Some(ExpCallKind::AdtConstructor),

                // INVALID: Trying to use a Statement inside an Expression!
                kind @ GlobalKind::Method | kind @ GlobalKind::StmtMacro => {
                    self.errors
                        .push(DisambiguationError::StatementCallInExpression(
                            call_tgt_name(),
                            kind,
                        ));
                }

                // INVALID: Targets that cannot be called at all (Fields, Domains, etc.)
                actual_kind => {
                    self.errors.push(DisambiguationError::NotCallable(
                        call_tgt_name(),
                        actual_kind,
                    ));
                }
            }
        } else {
            // UNRESOLVED IDENTIFIER
            self.errors
                .push(DisambiguationError::UnresolvedCallable(call_tgt_name()));
        }
    }

    fn walk_mut_exp_kind(&mut self, exp: &'_ mut ExpKind) {
        exp.walk_mut_children(self);

        match exp {
            // Expression-macro desugaring: bare ident → zero-arg macro call.
            ExpKind::Ident(name) => {
                let id = name.id();
                if let Some(sym) = self.globals.resolve(id)
                    && sym.kind() == GlobalKind::ExpMacro
                {
                    *exp = ExpKind::Call(crate::viper::Call {
                        kind: Some(ExpCallKind::Macro),
                        name: name.clone(),
                        args: Vec::new(),
                    });
                }
            }

            // Field-access classification: `e.f` is either a Viper field
            // access, an ADT discriminator (`e.is<Ctor>`), or (later) an ADT
            // destructor. Discriminators are recognised by the `is` prefix +
            // a known constructor; everything unrecognised is a field error.
            ExpKind::Field(base, field_name) => {
                let id = field_name.id();
                let is_field =
                    self.globals.resolve(id).map(|sym| sym.kind()) == Some(GlobalKind::Field);
                if is_field {
                    // ok — a genuine field access.
                } else if let Some(ctor) = self
                    .interner
                    .resolve(&id)
                    .strip_prefix("is")
                    .and_then(|c| self.globals.ctor_by_name.get(c))
                    .copied()
                {
                    // `e.is<Ctor>` → discriminator on `Ctor`.
                    let placeholder = Exp {
                        ty: InferenceType::Unknown,
                        kind: Box::new(ExpKind::Result),
                    };
                    let base = std::mem::replace(base, placeholder);
                    *exp = ExpKind::AdtDiscriminator(base, Ident::Interned(ctor));
                } else if self.globals.dtor_by_name.contains_key(&id) {
                    // `e.f` where `f` is an ADT destructor (constructor field).
                    let field_name = field_name.clone();
                    let placeholder = Exp {
                        ty: InferenceType::Unknown,
                        kind: Box::new(ExpKind::Result),
                    };
                    let base = std::mem::replace(base, placeholder);
                    *exp = ExpKind::AdtDestructor(base, field_name);
                } else {
                    let name = self.interner.resolve(&id).to_string();
                    match self.globals.resolve(id) {
                        Some(sym) => self
                            .errors
                            .push(DisambiguationError::NotAField(name, sym.kind())),
                        None => self.errors.push(DisambiguationError::UnknownField(name)),
                    }
                }
            }

            _ => {}
        }
    }
}

/// Disambiguate the parsed AST against `globals`: tag call nodes, demote
/// non-statement assignment RHSs, desugar macros, and validate field
/// accesses.
pub fn disambiguate(
    program: &mut crate::viper::Program,
    interner: &Interner,
    globals: &Globals,
) -> Result<(), Vec<DisambiguationError>> {
    let mut disambiguator = Disambiguator::new(interner, globals);
    program.walk_mut(&mut disambiguator);
    if disambiguator.errors.is_empty() {
        Ok(())
    } else {
        Err(disambiguator.errors)
    }
}
