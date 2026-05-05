use crate::{silver, vmir};
use lasso::Rodeo;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct ResolvedMethod {
    /// The method itself
    pub id: vmir::MemberId,
    /// The precondition resource, if any
    pub precond: Option<vmir::MemberId>,
    /// The postcondition resource, if any
    pub postcond: Option<vmir::MemberId>,
}

#[derive(Debug, Clone)]
pub struct ResolvedFunction {
    /// The function itself
    pub id: vmir::MemberId,
    /// The precondition resource, if any
    pub precond: Option<vmir::MemberId>,
    /// The postcondition function, if any
    pub postcond: Option<vmir::MemberId>,
}

#[derive(Debug, Clone)]
pub struct ResolvedField {
    /// The field function
    pub id: vmir::MemberId,
}

#[derive(Debug, Clone)]
pub struct ResolvedPredicate {
    /// The predicate resource
    pub id: vmir::MemberId,
    /// The snapshot domain/adt
    pub snap: vmir::MemberId,
}

#[derive(Debug, Clone)]
pub struct DuplicateGlobalError(pub String);

#[derive(Debug, Clone)]
pub enum ResolveError {
    UnknownName(String),
    MissingResolvedDecl {
        id: vmir::MemberId,
        kind: &'static str,
    },
}

// ==========================================
// Phase 1: Builder (Mutable)
// ==========================================

#[derive(Debug, Clone)]
pub struct GlobalResolverBuilder {
    silver_decls: HashMap<String, vmir::MemberId>,
    vmir_interner: Rodeo<vmir::MemberId>,

    methods: HashMap<vmir::MemberId, ResolvedMethod>,
    functions: HashMap<vmir::MemberId, ResolvedFunction>,
    fields: HashMap<vmir::MemberId, ResolvedField>,
    predicates: HashMap<vmir::MemberId, ResolvedPredicate>,
}

impl Default for GlobalResolverBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl GlobalResolverBuilder {
    pub fn new() -> Self {
        Self {
            silver_decls: HashMap::new(),
            vmir_interner: Rodeo::new(),
            methods: HashMap::new(),
            functions: HashMap::new(),
            fields: HashMap::new(),
            predicates: HashMap::new(),
        }
    }

    pub fn add_field(
        &mut self,
        field: &silver::Field,
    ) -> Result<&ResolvedField, DuplicateGlobalError> {
        let field_name = field.0.idn.0 .0.as_str();
        if self.silver_decls.contains_key(field_name) {
            return Err(DuplicateGlobalError(field_name.to_string()));
        }

        let field_func_id = self.vmir_interner.get_or_intern(field_name);
        self.silver_decls
            .insert(field_name.to_string(), field_func_id);

        Ok(self
            .fields
            .entry(field_func_id)
            .or_insert(ResolvedField { id: field_func_id }))
    }

    pub fn add_method(
        &mut self,
        method: &silver::Method,
    ) -> Result<&ResolvedMethod, DuplicateGlobalError> {
        let method_name = method.signature.name.0 .0.as_str();
        if self.silver_decls.contains_key(method_name) {
            return Err(DuplicateGlobalError(method_name.to_string()));
        }

        let method_id = self.vmir_interner.get_or_intern(method_name);

        let precond = method.contract.precondition.as_ref().map(|_| {
            self.vmir_interner
                .get_or_intern(format!("{method_name}@requires"))
        });

        let postcond = method.contract.postcondition.as_ref().map(|_| {
            self.vmir_interner
                .get_or_intern(format!("{method_name}@ensures"))
        });

        self.silver_decls.insert(method_name.to_string(), method_id);

        Ok(self.methods.entry(method_id).or_insert(ResolvedMethod {
            id: method_id,
            precond,
            postcond,
        }))
    }

    pub fn add_function(
        &mut self,
        function: &silver::Function,
    ) -> Result<&ResolvedFunction, DuplicateGlobalError> {
        let function_name = function.signature.name.0 .0.as_str();
        if self.silver_decls.contains_key(function_name) {
            return Err(DuplicateGlobalError(function_name.to_string()));
        }

        let function_id = self.vmir_interner.get_or_intern(function_name);
        self.silver_decls
            .insert(function_name.to_string(), function_id);

        Ok(self
            .functions
            .entry(function_id)
            .or_insert(ResolvedFunction {
                id: function_id,
                precond: None,
                postcond: None,
            }))
    }

    pub fn add_predicate(
        &mut self,
        predicate: &silver::Predicate,
    ) -> Result<&ResolvedPredicate, DuplicateGlobalError> {
        let predicate_name = predicate.signature.name.0 .0.as_str();
        if self.silver_decls.contains_key(predicate_name) {
            return Err(DuplicateGlobalError(predicate_name.to_string()));
        }

        let predicate_id = self.vmir_interner.get_or_intern(predicate_name);
        let snap_id = self
            .vmir_interner
            .get_or_intern(format!("{predicate_name}@snap"));

        self.silver_decls
            .insert(predicate_name.to_string(), predicate_id);

        Ok(self
            .predicates
            .entry(predicate_id)
            .or_insert(ResolvedPredicate {
                id: predicate_id,
                snap: snap_id,
            }))
    }

    /// Consumes the builder, returning the finalized resolver and the interner independently.
    pub fn finalize(self) -> (GlobalResolver, Rodeo<vmir::MemberId>) {
        let resolver = GlobalResolver {
            silver_decls: self.silver_decls,
            methods: self.methods,
            functions: self.functions,
            fields: self.fields,
            predicates: self.predicates,
        };

        (resolver, self.vmir_interner)
    }
}

// ==========================================
// Phase 2: Resolver (Immutable)
// ==========================================

#[derive(Debug, Clone)]
pub struct GlobalResolver {
    silver_decls: HashMap<String, vmir::MemberId>,
    methods: HashMap<vmir::MemberId, ResolvedMethod>,
    functions: HashMap<vmir::MemberId, ResolvedFunction>,
    fields: HashMap<vmir::MemberId, ResolvedField>,
    predicates: HashMap<vmir::MemberId, ResolvedPredicate>,
}

impl GlobalResolver {
    pub fn resolve_method(&self, ident: &silver::Ident) -> Result<&ResolvedMethod, ResolveError> {
        let name = ident.0.as_str();
        let id = self
            .silver_decls
            .get(name)
            .ok_or_else(|| ResolveError::UnknownName(name.to_string()))?;

        self.methods
            .get(id)
            .ok_or_else(|| ResolveError::MissingResolvedDecl {
                id: *id,
                kind: "method",
            })
    }

    pub fn resolve_function(
        &self,
        ident: &silver::Ident,
    ) -> Result<&ResolvedFunction, ResolveError> {
        let name = ident.0.as_str();
        let id = self
            .silver_decls
            .get(name)
            .ok_or_else(|| ResolveError::UnknownName(name.to_string()))?;

        self.functions
            .get(id)
            .ok_or_else(|| ResolveError::MissingResolvedDecl {
                id: *id,
                kind: "function",
            })
    }

    pub fn resolve_field(&self, ident: &silver::Ident) -> Result<&ResolvedField, ResolveError> {
        let name = ident.0.as_str();
        let id = self
            .silver_decls
            .get(name)
            .ok_or_else(|| ResolveError::UnknownName(name.to_string()))?;

        self.fields
            .get(id)
            .ok_or_else(|| ResolveError::MissingResolvedDecl {
                id: *id,
                kind: "field",
            })
    }

    pub fn resolve_predicate(
        &self,
        ident: &silver::Ident,
    ) -> Result<&ResolvedPredicate, ResolveError> {
        let name = ident.0.as_str();
        let id = self
            .silver_decls
            .get(name)
            .ok_or_else(|| ResolveError::UnknownName(name.to_string()))?;

        self.predicates
            .get(id)
            .ok_or_else(|| ResolveError::MissingResolvedDecl {
                id: *id,
                kind: "predicate",
            })
    }
}
