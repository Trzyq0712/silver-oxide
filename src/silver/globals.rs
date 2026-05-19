use std::{collections::HashMap, fmt};

use lasso::Spur;
use nonmax::NonMaxU32;
use typed_index_collections::TiVec;

use crate::silver::{IdnDecl, Type, interner::Interner, walk::AstWalker};

#[derive(Debug, Clone)]
pub struct FunctionSig {
    pub params: Vec<Type>,
    pub ret: Type,
}

#[derive(Debug, Clone)]
pub struct MethodSig {
    pub params: Vec<Type>,
    pub rets: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct PredicateSig {
    pub params: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct DomainSig {
    pub type_arity: usize,
}

#[derive(Debug, Clone)]
pub struct AdtSig {
    pub type_arity: usize,
}

#[derive(Debug, Clone)]
pub struct AdtConstructorSig {
    pub params: Vec<Type>,
    pub ret: Type,
}

#[derive(Debug, Clone)]
pub struct MacroSig {
    pub arity: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GlobalKind {
    Field,
    Predicate,
    Function,
    Method,
    Domain,
    Adt,
    AdtConstructor,
    ExpMacro,
    StmtMacro,
}

impl fmt::Display for GlobalKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Field => "field",
            Self::Predicate => "predicate",
            Self::Function => "function",
            Self::Method => "method",
            Self::Domain => "domain",
            Self::Adt => "ADT",
            Self::AdtConstructor => "ADT constructor",
            Self::ExpMacro => "macro",
            Self::StmtMacro => "macro",
        };
        write!(f, "{}", name)
    }
}

#[derive(Debug, Clone)]
pub enum GlobalSignature {
    Field(Type),
    Predicate(PredicateSig),
    Function(FunctionSig),
    Method(MethodSig),
    Domain(DomainSig),
    Adt(AdtSig),
    AdtConstructor(AdtConstructorSig),
    ExpMacro(MacroSig),
    StmtMacro(MacroSig),
}

impl GlobalSignature {
    pub fn kind(&self) -> GlobalKind {
        match self {
            Self::Field(_) => GlobalKind::Field,
            Self::Predicate(_) => GlobalKind::Predicate,
            Self::Function(_) => GlobalKind::Function,
            Self::Method(_) => GlobalKind::Method,
            Self::Domain(_) => GlobalKind::Domain,
            Self::Adt(_) => GlobalKind::Adt,
            Self::AdtConstructor(_) => GlobalKind::AdtConstructor,
            Self::ExpMacro(_) => GlobalKind::ExpMacro,
            Self::StmtMacro(_) => GlobalKind::StmtMacro,
        }
    }
}

impl From<GlobalSignature> for GlobalKind {
    fn from(sig: GlobalSignature) -> Self {
        sig.kind()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DuplicateGlobalError {
    pub name: String,
    pub this: GlobalKind,
    pub other: GlobalKind,
}

impl fmt::Display for DuplicateGlobalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Duplicate global definition: `{}` is defined as {}, but was already defined as {}",
            self.name, self.this, self.other
        )
    }
}

impl std::error::Error for DuplicateGlobalError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemberId(NonMaxU32);

impl From<MemberId> for usize {
    fn from(val: MemberId) -> Self {
        val.0.get() as usize
    }
}

impl From<usize> for MemberId {
    fn from(value: usize) -> Self {
        Self(NonMaxU32::new(value as u32).expect("MemberId overflow"))
    }
}

#[derive(Debug, Clone, Default)]
pub struct Globals {
    pub signatures: TiVec<MemberId, GlobalSignature>,
    pub symbol_table: HashMap<Spur, MemberId>,
}

impl Globals {
    pub fn lookup(&self, id: Spur) -> Option<MemberId> {
        self.symbol_table.get(&id).copied()
    }

    pub fn signature(&self, id: MemberId) -> &GlobalSignature {
        &self.signatures[id]
    }

    pub fn kind(&self, id: MemberId) -> GlobalKind {
        self.signatures[id].kind()
    }

    #[cold]
    #[track_caller]
    fn type_mismatch(expected: &str) -> ! {
        panic!(
            "Compiler Bug: Expected MemberId to resolve to a {} signature",
            expected
        );
    }

    pub fn function_sig(&self, id: MemberId) -> &FunctionSig {
        let GlobalSignature::Function(sig) = &self.signatures[id] else {
            Self::type_mismatch("Function")
        };
        sig
    }

    pub fn method_sig(&self, id: MemberId) -> &MethodSig {
        let GlobalSignature::Method(sig) = &self.signatures[id] else {
            Self::type_mismatch("Method")
        };
        sig
    }

    pub fn predicate_sig(&self, id: MemberId) -> &PredicateSig {
        let GlobalSignature::Predicate(sig) = &self.signatures[id] else {
            Self::type_mismatch("Predicate")
        };
        sig
    }

    pub fn field_sig(&self, id: MemberId) -> &Type {
        let GlobalSignature::Field(ty) = &self.signatures[id] else {
            Self::type_mismatch("Field")
        };
        ty
    }

    pub fn domain_sig(&self, id: MemberId) -> &DomainSig {
        let GlobalSignature::Domain(sig) = &self.signatures[id] else {
            Self::type_mismatch("Domain")
        };
        sig
    }

    pub fn adt_sig(&self, id: MemberId) -> &AdtSig {
        let GlobalSignature::Adt(sig) = &self.signatures[id] else {
            Self::type_mismatch("ADT")
        };
        sig
    }

    pub fn adt_constructor_sig(&self, id: MemberId) -> &AdtConstructorSig {
        let GlobalSignature::AdtConstructor(sig) = &self.signatures[id] else {
            Self::type_mismatch("ADT Constructor")
        };
        sig
    }

    pub fn macro_sig(&self, id: MemberId) -> &MacroSig {
        match &self.signatures[id] {
            GlobalSignature::ExpMacro(sig) | GlobalSignature::StmtMacro(sig) => sig,
            _ => Self::type_mismatch("Macro"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct GlobalsCollector<'i> {
    interner: &'i Interner,
    signatures: TiVec<MemberId, GlobalSignature>,
    symbol_table: HashMap<Spur, MemberId>,
    errors: Vec<DuplicateGlobalError>,
}

impl<'i> GlobalsCollector<'i> {
    pub fn new(interner: &'i Interner) -> Self {
        Self {
            interner,
            signatures: TiVec::new(),
            symbol_table: HashMap::new(),
            errors: Vec::new(),
        }
    }

    pub fn finalize(self) -> Result<Globals, Vec<DuplicateGlobalError>> {
        if self.errors.is_empty() {
            Ok(Globals {
                signatures: self.signatures,
                symbol_table: self.symbol_table,
            })
        } else {
            Err(self.errors)
        }
    }

    fn register(&mut self, name: &IdnDecl, sig: GlobalSignature) -> Option<MemberId> {
        let id = name.0.id();
        if let Some(&mid) = self.symbol_table.get(&id) {
            self.errors.push(DuplicateGlobalError {
                name: self.interner.resolve(&id).to_string(),
                this: sig.kind(),
                other: self.signatures[mid].kind(),
            });
            None
        } else {
            let mid = self.signatures.push_and_get_key(sig);
            self.symbol_table.insert(id, mid);
            Some(mid)
        }
    }
}

impl<'ast, 'i> AstWalker<'ast> for GlobalsCollector<'i> {
    fn walk_field(&mut self, field: &'ast super::Field) {
        self.register(&field.0.idn, GlobalSignature::Field(field.0.ty.clone()));
    }

    fn walk_predicate(&mut self, pred: &'ast super::Predicate) {
        let sig = PredicateSig {
            params: pred.signature.args.iter().map(|p| p.ty().clone()).collect(),
        };
        self.register(&pred.signature.name, GlobalSignature::Predicate(sig));
    }

    fn walk_function(&mut self, func: &'ast super::Function) {
        let sig = FunctionSig {
            params: func.signature.args.iter().map(|p| p.ty().clone()).collect(),
            ret: func.signature.ret[0].ty().clone(),
        };
        self.register(&func.signature.name, GlobalSignature::Function(sig));
    }

    fn walk_method(&mut self, method: &'ast super::Method) {
        let sig = MethodSig {
            params: method
                .signature
                .args
                .iter()
                .map(|p| p.ty().clone())
                .collect(),
            rets: method
                .signature
                .ret
                .iter()
                .map(|r| r.ty().clone())
                .collect(),
        };
        self.register(&method.signature.name, GlobalSignature::Method(sig));
    }

    fn walk_domain(&mut self, domain: &'ast super::Domain) {
        let sig = DomainSig {
            type_arity: domain.params.len(),
        };
        self.register(&domain.name, GlobalSignature::Domain(sig));
    }

    fn walk_adt(&mut self, adt: &'ast super::Adt) {
        let sig = AdtSig {
            type_arity: adt.params.len(),
        };
        self.register(&adt.name, GlobalSignature::Adt(sig));
    }

    fn walk_adt_constructor(&mut self, adt_cons: &'ast super::AdtConstructor) {
        let sig = AdtConstructorSig {
            params: adt_cons
                .signature
                .args
                .iter()
                .map(|p| p.ty().clone())
                .collect(),
            ret: adt_cons.signature.ret[0].ty().clone(),
        };
        self.register(
            &adt_cons.signature.name,
            GlobalSignature::AdtConstructor(sig),
        );
    }

    fn walk_domain_function(&mut self, func: &'ast super::DomainFunction) {
        let sig = FunctionSig {
            params: func.signature.args.iter().map(|p| p.ty().clone()).collect(),
            ret: func.signature.ret[0].ty().clone(),
        };
        self.register(&func.signature.name, GlobalSignature::Function(sig));
    }

    fn walk_define(&mut self, define: &'ast super::Define) {
        let sig = MacroSig {
            arity: define.args.len(),
        };

        let sig_enum = match define.body {
            super::ExpOrBlock::Exp(_) => GlobalSignature::ExpMacro(sig),
            super::ExpOrBlock::Block(_) => GlobalSignature::StmtMacro(sig),
        };

        self.register(&define.name, sig_enum);
    }
}
