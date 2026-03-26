//! Translation from Silver (Viper) AST to VMIR AST.
//!
//! This module implements the translation of Viper programs into VMIR, an intermediate
//! representation. The key transformations are:
//!
//! - **Fields** → Functions returning addresses: `field v: Int` becomes a function that
//!   takes a `Ref` and returns `Addr<Int>`.
//!
//! - **Predicates** → Functions returning resource addresses + Resource declarations:
//!   ```
//!   predicate pr_(x1: Ref, x2: Ref, i: Int) { ... }
//!   ```
//!   becomes:
//!   ```
//!   function pr_(Ref, Ref, Int): Addr<pr__heap>
//!   resource pr__heap(Ref, Ref, Int) { ... } with { ... }
//!   ```
//!   The function returns an address to the resource type, and a corresponding resource
//!   declaration is created with the predicate body split into permissions and assertions.
//!
//! - **Methods** → Methods with translated signatures and contracts.
//!
//! Note: This implementation uses de Bruijn indices for variable references,
//! so parameter names are not stored in the VMIR signatures.

use crate::silver;
use crate::vmir;
use typed_index_collections::TiVec;

pub struct VmirTranslator {
    pub program: vmir::Program,
}

impl VmirTranslator {
    pub fn new() -> Self {
        VmirTranslator {
            program: vmir::Program(TiVec::new()),
        }
    }

    fn translate_type(&self, ty: &silver::Type) -> vmir::Type {
        match ty {
            silver::Type::Bool => vmir::Type::Bool,
            silver::Type::Int => vmir::Type::Int,
            silver::Type::Real => vmir::Type::Real,
            silver::Type::Ref => vmir::Type::Ref,
            silver::Type::Domain(_, _) => vmir::Type::Domain,
        }
    }

    fn translate_signature_to_types(
        &self,
        sig: &silver::Signature,
    ) -> (Vec<vmir::Type>, Vec<vmir::Type>) {
        let args = sig
            .args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();
        let ret = sig
            .ret
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();
        (args, ret)
    }

    fn translate_field(&mut self, field: &silver::Field) {
        // field v: Int -> function v(...): Addr<Int>
        let silver::Field(sig) = field;
        let (args, ret) = self.translate_signature_to_types(sig);

        // Field returns an address to the field type
        let ret_type = if ret.len() == 1 {
            vmir::Type::Addr(Box::new(ret[0].clone()))
        } else {
            panic!("Field must have exactly one return type");
        };

        let vmir_sig = vmir::Signature {
            name: vmir::IdnDecl(vmir::Ident(sig.name.0 .0.clone())),
            args,
            ret: vec![ret_type],
        };

        let function = vmir::Function {
            signature: vmir_sig,
            contract: vmir::Contract,
            body: None,
        };

        self.program.0.push(vmir::Declaration::Function(function));
    }

    fn translate_predicate(&mut self, predicate: &silver::Predicate) {
        // predicate pr_(x1: Ref, x2: Ref, i: Int) { body } translates to:
        // 1. function pr_(x1: Ref, x2: Ref, i: Int): Addr<pr_heap>
        // 2. resource pr_heap(x1: Ref, x2: Ref, i: Int) { ... }
        
        let (args, _) = self.translate_signature_to_types(&predicate.signature);
        
        // Generate the resource name by appending "_heap" to the predicate name
        let resource_name = format!("{}_heap", predicate.signature.name.0.0);
        
        // Create the function that returns an address to the resource
        let func_sig = vmir::Signature {
            name: vmir::IdnDecl(vmir::Ident(predicate.signature.name.0 .0.clone())),
            args: args.clone(),
            ret: vec![vmir::Type::Addr(Box::new(vmir::Type::Resource(vmir::Ident(resource_name.clone()))))],
        };

        let function = vmir::Function {
            signature: func_sig,
            contract: vmir::Contract,
            body: None,
        };

        self.program.0.push(vmir::Declaration::Function(function));

        // Create the resource declaration
        let resource = vmir::Resource {
            name: vmir::IdnDecl(vmir::Ident(resource_name)),
            args,
            body: if predicate.body.is_some() {
                Some(vmir::ResourceBody {})
            } else {
                None
            },
        };

        self.program.0.push(vmir::Declaration::Resource(resource));
    }

    fn translate_method(&mut self, method: &silver::Method) {
        let (args, ret) = self.translate_signature_to_types(&method.signature);

        let vmir_sig = vmir::Signature {
            name: vmir::IdnDecl(vmir::Ident(method.signature.name.0 .0.clone())),
            args,
            ret,
        };

        let vmir_method = vmir::Method {
            signature: vmir_sig,
            contract: vmir::Contract,
            body: None, // TODO: translate method body
        };

        self.program.0.push(vmir::Declaration::Method(vmir_method));
    }
}

impl<'a> silver::walk::AstWalker<'a> for VmirTranslator {
    fn walk_program(&mut self, prog: &'a silver::Program) {
        for decl in &prog.0 {
            match decl {
                silver::Declaration::Import(_) => {
                    // Skip imports for now
                }
                silver::Declaration::Define(_) => {
                    // Skip defines for now
                }
                silver::Declaration::Domain(_) => {
                    // Skip domains for now
                }
                silver::Declaration::DomainElement(_) => {
                    // Skip domain elements for now
                }
                silver::Declaration::Field(field) => {
                    self.translate_field(field);
                }
                silver::Declaration::Function(_) => {
                    // Skip functions for now
                }
                silver::Declaration::Predicate(predicate) => {
                    self.translate_predicate(predicate);
                }
                silver::Declaration::Method(method) => {
                    self.translate_method(method);
                }
                silver::Declaration::Adt(_) => {
                    // Skip ADTs for now
                }
                silver::Declaration::AdtConstructor(_) => {
                    // Skip ADT constructors for now
                }
            }
        }
    }
}
