use crate::silver;
use crate::silver::walk::{AstWalkable, AstWalker};
use crate::vmir::{self, MemberId, Type};
use lasso::Rodeo;
use std::collections::HashMap;
use typed_index_collections::TiVec;

/// Stores type signature information for all declarations
/// This is populated in a separate pass before translating bodies
#[derive(Debug, Clone)]
pub struct SignatureContext {
    /// Function signatures: args and single return type
    /// Also includes predicates and fields (which are functions returning addresses)
    pub functions: HashMap<MemberId, FunctionSignature>,
    /// Method signatures: args and multiple return types
    pub methods: HashMap<MemberId, MethodSignature>,
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub args: Vec<Type>,
    pub ret: Type,
}

#[derive(Debug, Clone)]
pub struct MethodSignature {
    pub args: Vec<Type>,
    pub ret: Vec<Type>,
}

impl SignatureContext {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            methods: HashMap::new(),
        }
    }

    /// Collect all signatures from a Silver program
    pub fn collect(
        program: &silver::Program,
        interner: &Rodeo<MemberId>,
    ) -> Self {
        let mut collector = SignatureCollector {
            context: SignatureContext::new(),
            interner,
        };
        program.walk(&mut collector);
        collector.context
    }

    /// Get the return type of a function (includes predicates and fields)
    pub fn get_function_return_type(&self, func_id: MemberId) -> Option<&Type> {
        self.functions.get(&func_id).map(|sig| &sig.ret)
    }
}

struct SignatureCollector<'a> {
    context: SignatureContext,
    interner: &'a Rodeo<MemberId>,
}

impl<'a> SignatureCollector<'a> {
    fn translate_type(&self, ty: &silver::Type) -> Type {
        match ty {
            silver::Type::Bool => Type::Bool,
            silver::Type::Int => Type::Int,
            silver::Type::Real => Type::Real,
            silver::Type::Ref => Type::Ref,
            silver::Type::Domain(ident, _) => {
                let domain_id = self.interner
                    .get(&ident.0)
                    .expect("Domain name should be interned");
                Type::Domain(domain_id)
            }
        }
    }
}

impl<'a, 'b> AstWalker<'b> for SignatureCollector<'a> {
    fn walk_field(&mut self, field: &'b silver::Field) {
        let silver::Field(decl) = field;
        let name = &decl.idn.0 .0;
        
        let field_id = self.interner
            .get(name)
            .expect("Field name should be interned");
        
        let field_type = self.translate_type(&decl.ty);
        
        // Field is a function returning an address to the field type
        let ret_type = Type::Addr(Box::new(field_type));
        
        self.context.functions.insert(
            field_id,
            FunctionSignature {
                args: vec![Type::Ref], // Field accessor takes a Ref
                ret: ret_type,
            },
        );
    }

    fn walk_function(&mut self, function: &'b silver::Function) {
        let sig = &function.signature;
        let name = &sig.name.0 .0;
        
        let func_id = self.interner
            .get(name)
            .expect("Function name should be interned");
        
        let args: Vec<_> = sig.args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();
        
        let ret = if sig.ret.is_empty() {
            Type::Bool // Default for no return type
        } else {
            self.translate_type(sig.ret[0].ty())
        };
        
        self.context.functions.insert(
            func_id,
            FunctionSignature { args, ret },
        );
    }

    fn walk_method(&mut self, method: &'b silver::Method) {
        let sig = &method.signature;
        let name = &sig.name.0 .0;
        
        let method_id = self.interner
            .get(name)
            .expect("Method name should be interned");
        
        let args: Vec<_> = sig.args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();
        
        let ret: Vec<_> = sig.ret
            .iter()
            .map(|r| self.translate_type(r.ty()))
            .collect();
        
        self.context.methods.insert(
            method_id,
            MethodSignature { args, ret },
        );
    }

    fn walk_predicate(&mut self, predicate: &'b silver::Predicate) {
        let sig = &predicate.signature;
        let name = &sig.name.0 .0;
        
        let pred_id = self.interner
            .get(name)
            .expect("Predicate name should be interned");
        
        let args: Vec<_> = sig.args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();
        
        // Compute snapshot domain name
        let snap_name = format!("{}@snap", name);
        let snap_id = self.interner
            .get(&snap_name)
            .expect("Snapshot name should be interned");
        
        // Predicate is a function returning address to snapshot domain
        let ret = Type::Addr(Box::new(Type::Domain(snap_id)));
        
        self.context.functions.insert(
            pred_id,
            FunctionSignature { args, ret },
        );
    }
}
