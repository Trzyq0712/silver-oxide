use crate::vmir;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSignature {
    pub args: Vec<vmir::Type>,
    pub ret: vmir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceSignature {
    pub args: Vec<vmir::Type>,
}

#[derive(Debug, Clone)]
pub struct MissingResourceError(pub vmir::MemberId);

#[derive(Debug, Clone)]
pub struct MissingFunctionError(pub vmir::MemberId);

// ==========================================
// Phase 1: Builder (Mutable)
// ==========================================

#[derive(Debug, Clone)]
pub struct SignatureResolverBuilder {
    functions: HashMap<vmir::MemberId, FunctionSignature>,
    resources: HashMap<vmir::MemberId, ResourceSignature>,
}

impl Default for SignatureResolverBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SignatureResolverBuilder {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            resources: HashMap::new(),
        }
    }

    /// Registers a new function signature.
    pub fn add_function(
        &mut self,
        id: vmir::MemberId,
        args: Vec<vmir::Type>,
        ret: vmir::Type,
    ) -> &FunctionSignature {
        self.functions
            .entry(id)
            .or_insert(FunctionSignature { args, ret })
    }

    /// Registers a new resource signature.
    pub fn add_resource(
        &mut self,
        id: vmir::MemberId,
        args: Vec<vmir::Type>,
    ) -> &ResourceSignature {
        self.resources
            .entry(id)
            .or_insert(ResourceSignature { args })
    }

    /// Consumes the builder, returning the finalized immutable resolver.
    pub fn finalize(self) -> SignatureResolver {
        SignatureResolver {
            functions: self.functions,
            resources: self.resources,
        }
    }
}

// ==========================================
// Phase 2: Resolver (Immutable)
// ==========================================

#[derive(Debug, Clone)]
pub struct SignatureResolver {
    functions: HashMap<vmir::MemberId, FunctionSignature>,
    resources: HashMap<vmir::MemberId, ResourceSignature>,
}

impl SignatureResolver {
    /// Retrieves a function signature.
    pub fn resolve_function(
        &self,
        id: vmir::MemberId,
    ) -> Result<&FunctionSignature, MissingFunctionError> {
        self.functions.get(&id).ok_or(MissingFunctionError(id))
    }

    /// Retrieves a resource signature.
    pub fn resolve_resource(
        &self,
        id: vmir::MemberId,
    ) -> Result<&ResourceSignature, MissingResourceError> {
        self.resources.get(&id).ok_or(MissingResourceError(id))
    }
}
