use crate::silver;
use crate::silver::walk::AstWalkable;
use crate::translate::name_resolution::DeclKind;
use crate::vmir::{self, exp, MemberId};
use lasso::{Key, Rodeo};
use nonmax::NonMaxU32;
use rusttyc::{TcKey, TcVar, TypeChecker};
use std::collections::HashMap;
use typed_index_collections::{ti_vec, TiVec};

// TODO: Type Checking Phase
// Currently, type inference is done inline during expression translation.
// For more sophisticated type checking (especially with generics in domains),
// consider adding rusttyc or a similar type checking library.
// This would be a separate pass before translation:
//   1. Name Resolution (current: NameCollector)
//   2. Type Checking (future: using rusttyc or custom implementation)
//   3. Translation to VMIR (current: VmirTranslator)
//
// Type checking would:
//   - Verify all expressions are well-typed
//   - Resolve type variables in generic domains
//   - Check function call argument types
//   - Infer missing type annotations
//   - Build a type environment that translation can use

pub mod name_resolution;
pub mod signatures;
pub mod typecheck;
pub use name_resolution::{IdentifierError, NameCollector};
pub use signatures::SignatureContext;

pub struct VmirTranslator {
    globals: TiVec<MemberId, Option<vmir::Declaration>>,
    interner: Rodeo<MemberId>,
    name_kinds: TiVec<MemberId, DeclKind>,
    signatures: SignatureContext,
}

/// Context for translating expressions within a function/method
/// This tracks locals, generates SSA instructions, and accumulates type information
struct ExpTranslationContext<'a, 'b> {
    /// Maps Silver variable names to VMIR local indices
    locals: HashMap<&'b str, NonMaxU32>,
    /// Current instruction list being built
    /// Stores (InstKind, initial type, TcKey for resolving)
    insts: Vec<(exp::InstKind, typecheck::Type, TcKey)>,

    tc: TypeChecker<typecheck::Type, vmir::exp::Value>,
    /// Current impure access expressions (acc(...))
    impures: Vec<exp::Acc>,
    /// Counter for generating temporary indices
    temp_counter: u32,
    /// Reference to the translator for looking up global names
    translator: &'a VmirTranslator,
}

impl TcVar for vmir::exp::Value {}

impl<'a, 'b> ExpTranslationContext<'a, 'b> {
    fn new(
        translator: &'a VmirTranslator,
        locals: impl IntoIterator<Item = (&'b silver::IdnDecl, vmir::Type)>,
    ) -> Self {
        let mut name_idx_map = HashMap::new();
        let mut tc = TypeChecker::new();
        for (idx, (name, ty)) in locals.into_iter().enumerate() {
            let idx = NonMaxU32::new(idx as u32).expect("Too many parameters");
            let ty = typecheck::Type::from_vmir_type(&ty);
            name_idx_map.insert(name.0 .0.as_str(), idx);
            let tc_key = tc.get_var_key(&vmir::exp::Value::Local(idx));
            tc.impose(tc_key.concretizes_explicit(ty)).unwrap();
        }

        Self {
            locals: name_idx_map,
            insts: Vec::new(),
            tc,
            impures: Vec::new(),
            temp_counter: 0,
            translator,
        }
    }

    /// Generate a new temporary index
    fn fresh_temp(&mut self) -> NonMaxU32 {
        let temp = NonMaxU32::new(self.temp_counter).expect("Too many temporaries");
        self.temp_counter += 1;
        temp
    }

    /// Add an instruction and return the temporary holding its result
    fn add_inst(&mut self, kind: exp::InstKind, ty: typecheck::Type) -> exp::Value {
        let temp = self.fresh_temp();
        let val = exp::Value::Temp(temp);
        
        // Impose constraint on the result value and get the key
        let key = self.tc.get_var_key(&val);
        self.tc.impose(key.concretizes_explicit(ty.clone())).unwrap();
        
        self.insts.push((kind, ty, key));
        val
    }

    /// Finalize the expression into a VMIR Exp
    /// This resolves all type constraints and converts typecheck types to VMIR types
    fn finalize(self, res: exp::Value) -> exp::Exp {
        // Run type checking to resolve all constraints
        let type_table = self.tc.type_check_preliminary()
            .expect("Type checking failed");
        
        // Convert instructions, resolving types using stored keys
        let insts = self.insts.into_iter().map(|(kind, _, key)| {
            let resolved_ty = &type_table[&key].variant;
            exp::Inst {
                kind,
                ty: resolved_ty.to_vmir_type(),
            }
        }).collect();
        
        exp::Exp {
            insts,
            res,
            impures: self.impures,
        }
    }
}

impl VmirTranslator {
    /// Create a new translator with a pre-populated interner from name collection.
    pub fn new(
        interner: Rodeo<MemberId>,
        name_kinds: TiVec<MemberId, DeclKind>,
        signatures: SignatureContext,
    ) -> Self {
        let num_declarations = interner.len();
        VmirTranslator {
            // Preallocate the vector with None placeholders
            globals: ti_vec![None; num_declarations],
            interner,
            name_kinds,
            signatures,
        }
    }

    /// Translate a Silver program to VMIR.
    /// This is a three-pass process:
    /// 1. Collect and intern all names (detecting duplicates)
    /// 2. Collect type signatures for all declarations
    /// 3. Translate declarations using the full context
    pub fn translate(program: &silver::Program) -> Result<vmir::Program, Vec<IdentifierError>> {
        // First pass: collect and intern all global names
        let collector = NameCollector::new();
        let (interner, name_kinds) = collector.collect(program)?;

        // Second pass: collect all type signatures
        let signatures = SignatureContext::collect(program, &interner);

        // Third pass: translate with the populated interner and signatures
        let mut translator = Self::new(interner, name_kinds, signatures);
        program.walk(&mut translator);

        let decls = translator
            .globals
            .into_iter()
            .enumerate()
            .map(|(idx, decl)| {
                decl.unwrap_or_else(|| panic!("Declaration at index {} was not translated", idx))
            })
            .collect();

        Ok(vmir::Program {
            decls,
            interner: translator.interner,
        })
    }

    fn translate_type(&self, ty: &silver::Type) -> vmir::Type {
        match ty {
            silver::Type::Bool => vmir::Type::Bool,
            silver::Type::Int => vmir::Type::Int,
            silver::Type::Real => vmir::Type::Real,
            silver::Type::Ref => vmir::Type::Ref,
            silver::Type::Domain(ident, _) => vmir::Type::Domain(
                self.interner
                    .get(&ident.0)
                    .expect("Domain name should be interned"),
            ),
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
        // field v: Int -> function v(Ref): &Int
        let silver::Field(decl) = field;

        let ident = decl.idn.0 .0.as_str();
        // The name should already be interned from the first pass
        let member_id = self
            .interner
            .get(ident)
            .expect("Name should be pre-interned");

        // For fields, we need to create a function signature with Ref as argument
        let args = vec![self.translate_type(&silver::Type::Ref)];
        let ret = self.translate_type(&decl.ty);
        // Field returns an address to the field type
        let ret = vmir::Type::Addr(Box::new(ret));

        let func = vmir::Function {
            name: member_id,
            signature: vmir::FuncSig { args, ret },
            contract: vmir::FuncContract::empty(),
            body: None,
        };

        // Insert at the correct index
        assert!(
            self.globals[member_id].is_none(),
            "Declaration at index {} already exists",
            member_id.into_usize()
        );
        self.globals[member_id] = Some(vmir::Declaration::Function(func));
    }

    fn translate_predicate(&mut self, predicate: &silver::Predicate) {
        // predicate pr(x: Ref, i: Int) { body } translates to:
        // 1. function pr(x: Ref, i: Int): &pr_snap
        // 2. resource pr_heap(x: Ref, i: Int) { ... }  // TODO
        // 3. Is body present:
        //    - Yes --> adt pr_snap { ... }  // TODO: translate body fields
        //    - No  --> domain pr_snap { }

        let sig = &predicate.signature;
        let ident = sig.name.0 .0.as_str();

        // Create snapshot type (domain or adt depending on whether body exists)
        let snap_name = format!("{}@snap", ident);
        let snap_id = self.interner.get_or_intern(&snap_name);

        let snap_decl = match predicate.body {
            None => {
                let domain = vmir::Domain { name: snap_id };
                vmir::Declaration::Domain(domain)
            }
            Some(ref body) => {
                // TODO: When translating the predicate body:
                // 1. Create an ExpTranslationContext with predicate parameters as locals
                // 2. Use translate_complete_exp to translate body.0 (the Exp)
                // 3. Extract impures (acc expressions) to build the ADT snapshot
                //
                // Example:
                // let vmir_exp = self.translate_complete_exp(&body.0);
                // // vmir_exp.impures contains all acc(...) expressions
                // // These become fields in the snapshot ADT

                let adt = vmir::Adt { name: snap_id };
                vmir::Declaration::Adt(adt)
            }
        };

        // Store the snapshot declaration
        let snap_member_id = snap_id;
        assert!(
            self.globals[snap_member_id].is_none(),
            "Declaration at index {} already exists",
            snap_member_id.into_usize()
        );
        self.globals[snap_member_id] = Some(snap_decl);

        // Create a function for returning the snapshot address
        let func_member_id = self
            .interner
            .get(ident)
            .expect("Name should be pre-interned");

        let args: Vec<_> = sig
            .args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();

        let ret = vmir::Type::Addr(Box::new(vmir::Type::Domain(snap_member_id)));

        let func = vmir::Function {
            name: func_member_id,
            signature: vmir::FuncSig {
                args: args.clone(),
                ret,
            },
            contract: vmir::FuncContract::empty(),
            body: None,
        };
        assert!(
            self.globals[func_member_id].is_none(),
            "Declaration at index {} already exists",
            func_member_id.into_usize()
        );
        self.globals[func_member_id] = Some(vmir::Declaration::Function(func));

        // Create the resource declaration for the predicate
        let resource_name = format!("{}@heap", ident);
        let resource_id = self.interner.get_or_intern(&resource_name);

        let resource = vmir::Resource {
            name: resource_id,
            args,
            snapshot: snap_member_id,
            body: predicate
                .body
                .as_ref()
                .map(|body| self.translate_complete_exp_with_locals(&body.0.exp, &sig.args)),
        };

        assert!(
            self.globals[resource_id].is_none(),
            "Declaration at index {} already exists",
            resource_id.into_usize()
        );
        self.globals[resource_id] = Some(vmir::Declaration::Resource(resource));
    }

    fn translate_const(&self, const_: &silver::ConstKind) -> exp::Literal {
        match const_ {
            silver::ConstKind::Bool(b) => exp::Literal::Bool(*b),
            silver::ConstKind::Int(i) => exp::Literal::Int(i.clone()),
            silver::ConstKind::Real(r) => exp::Literal::Real(r.clone()),
            silver::ConstKind::Null => exp::Literal::Null,
            _ => unimplemented!("Unsupported constant: {:?}", const_),
        }
    }

    /// Translate a Silver expression to VMIR SSA form
    /// Returns the Value representing the result and the inferred type
    fn translate_exp(
        &self,
        exp: &silver::Exp,
        ctx: &mut ExpTranslationContext,
    ) -> (exp::Value, typecheck::Type) {
        use silver::ExpKind;

        match exp.as_ref() {
            ExpKind::Const(const_) => {
                let ty = match const_ {
                    silver::ConstKind::Bool(_) => typecheck::Type::Bool,
                    silver::ConstKind::Int(_) => typecheck::Type::Int,
                    silver::ConstKind::Real(_) => typecheck::Type::Real,
                    silver::ConstKind::Null => typecheck::Type::Ref,
                    _ => unimplemented!("Constant type inference: {:?}", const_),
                };
                (
                    exp::Value::Const(self.translate_const(const_)),
                    ty,
                )
            }

            ExpKind::Ident(ident) => {
                // Look up in locals
                if let Some(&local_idx) = ctx.locals.get(ident.0.as_str()) {
                    let val = exp::Value::Local(local_idx);
                    // The type was already imposed in the context constructor
                    // We can query it from the type checker
                    let key = ctx.tc.get_var_key(&val);
                    // Type will be resolved at finalize time
                    // For now, just return Top as a placeholder
                    (val, typecheck::Type::Top)
                } else {
                    panic!("Undefined variable: {}", ident.0);
                }
            }

            ExpKind::BinOp(op, left, right) => {
                // Desugar logical operators into ternaries
                match op {
                    silver::BinOp::And => {
                        // a && b  =>  a ? b : false
                        let (cond_val, _) = self.translate_exp(left, ctx);
                        let (then_val, _) = self.translate_exp(right, ctx);
                        let else_val = exp::Value::Const(exp::Literal::Bool(false));

                        let val = ctx.add_inst(
                            exp::InstKind::Ternary(cond_val, then_val, else_val),
                            typecheck::Type::Bool,
                        );
                        (val, typecheck::Type::Bool)
                    }

                    silver::BinOp::Or => {
                        // a || b  =>  a ? true : b
                        let (cond_val, _) = self.translate_exp(left, ctx);
                        let then_val = exp::Value::Const(exp::Literal::Bool(true));
                        let (else_val, _) = self.translate_exp(right, ctx);

                        let val = ctx.add_inst(
                            exp::InstKind::Ternary(cond_val, then_val, else_val),
                            typecheck::Type::Bool,
                        );
                        (val, typecheck::Type::Bool)
                    }

                    silver::BinOp::Implies => {
                        // a ==> b  =>  a ? b : true
                        let (cond_val, _) = self.translate_exp(left, ctx);
                        let (then_val, _) = self.translate_exp(right, ctx);
                        let else_val = exp::Value::Const(exp::Literal::Bool(true));

                        let val = ctx.add_inst(
                            exp::InstKind::Ternary(cond_val, then_val, else_val),
                            typecheck::Type::Bool,
                        );
                        (val, typecheck::Type::Bool)
                    }

                    _ => {
                        // Regular binary operations
                        let (left_val, left_ty) = self.translate_exp(left, ctx);
                        let (right_val, right_ty) = self.translate_exp(right, ctx);

                        // Determine the result type based on the operator
                        let result_ty = match op {
                            silver::BinOp::Iff => typecheck::Type::Bool,
                            silver::BinOp::Eq
                            | silver::BinOp::Neq
                            | silver::BinOp::Lt
                            | silver::BinOp::Le
                            | silver::BinOp::Gt
                            | silver::BinOp::Ge => typecheck::Type::Bool,
                            
                            // Division produces Numeric type (can be Int or Real)
                            silver::BinOp::Div => typecheck::Type::Numeric,
                            
                            silver::BinOp::Plus
                            | silver::BinOp::Minus
                            | silver::BinOp::Mult
                            | silver::BinOp::Mod
                            | silver::BinOp::IntDiv => {
                                // Arithmetic operations: result is meet of operand types
                                let left_key = ctx.tc.get_var_key(&left_val);
                                let right_key = ctx.tc.get_var_key(&right_val);
                                let result = ctx.tc.new_term_key();
                                ctx.tc.impose(result.is_meet_of(left_key, right_key)).unwrap();
                                
                                // Return the left type as placeholder (will be resolved)
                                left_ty.clone()
                            }
                            _ => unimplemented!("BinOp type inference: {:?}", op),
                        };

                        let vmir_op = self.translate_binop(op);
                        let val = ctx.add_inst(
                            exp::InstKind::Binary(vmir_op, left_val, right_val),
                            result_ty.clone(),
                        );
                        (val, result_ty)
                    }
                }
            }

            ExpKind::UnOp(op, inner) => {
                let (inner_val, inner_ty) = self.translate_exp(inner, ctx);

                let result_ty = match op {
                    silver::UnOp::Not => typecheck::Type::Bool,
                    silver::UnOp::Neg => inner_ty.clone(),
                    _ => unimplemented!("UnOp type inference: {:?}", op),
                };

                let vmir_op = self.translate_unop(op);
                let val = ctx.add_inst(exp::InstKind::Unary(vmir_op, inner_val), result_ty.clone());
                (val, result_ty)
            }

            ExpKind::Ternary(cond, then_exp, else_exp) => {
                let (cond_val, _) = self.translate_exp(cond, ctx);
                let (then_val, then_ty) = self.translate_exp(then_exp, ctx);
                let (else_val, _) = self.translate_exp(else_exp, ctx);

                let val = ctx.add_inst(
                    exp::InstKind::Ternary(cond_val, then_val, else_val),
                    then_ty.clone(),
                );
                (val, then_ty)
            }

            func_app @ ExpKind::FuncApp(func_name, args) => {
                let func_id = self
                    .interner
                    .get(&func_name.0)
                    .expect(&format!("Function {} not found", func_name.0));

                // Check if this is a predicate call
                let is_predicate = self
                    .name_kinds
                    .get(func_id)
                    .map(|kind| *kind == DeclKind::Predicate)
                    .unwrap_or(false);

                if is_predicate {
                    // Desugar predicate(args) into acc(predicate(args), write)
                    let acc_exp = silver::AccExp {
                        acc: silver::LocAccess {
                            loc: Box::new(func_app.clone()),
                        },
                        perm: Box::new(ExpKind::Const(silver::ConstKind::Real(
                            num::BigRational::from_integer(1.into()),
                        ))),
                    };

                    self.translate_acc_exp(&acc_exp, ctx)
                } else {
                    self.translate_func_app((func_name, args), ctx)
                }
            }

            ExpKind::Field(base, field_name) => {
                let (base_val, _) = self.translate_exp(base, ctx);

                // Look up the field in the interner
                let field_id = self
                    .interner
                    .get(&field_name.0)
                    .expect(&format!("Field {} not found", field_name.0));

                // Get field signature and convert to typecheck type
                let result_ty = self
                    .signatures
                    .get_function_return_type(field_id)
                    .map(|ty| typecheck::Type::from_vmir_type(ty))
                    .unwrap_or_else(|| typecheck::Type::AddrOf(Box::new(typecheck::Type::Int))); // Fallback

                let val = ctx.add_inst(
                    exp::InstKind::Call(field_id, vec![base_val]),
                    result_ty.clone(),
                );
                (val, result_ty)
            }

            ExpKind::Acc(acc_exp) => self.translate_acc_exp(acc_exp, ctx),

            _ => unimplemented!("Expression translation: {:?}", exp),
        }
    }

    fn translate_func_app(
        &self,
        (func_name, args): (&silver::Ident, &Vec<silver::Exp>),
        ctx: &mut ExpTranslationContext,
    ) -> (exp::Value, typecheck::Type) {
        let func_id = self
            .interner
            .get(&func_name.0)
            .expect(&format!("Function {} not found", func_name.0));

        let arg_vals: Vec<_> = args
            .iter()
            .map(|arg| self.translate_exp(arg, ctx).0)
            .collect();

        // Look up return type from signature context
        // All callables (functions, predicates, fields) are stored in functions map
        let result_ty = self
            .signatures
            .get_function_return_type(func_id)
            .map(|ty| typecheck::Type::from_vmir_type(ty))
            .unwrap_or_else(|| panic!("No signature found for callable: {}", func_name.0));

        let val = ctx.add_inst(exp::InstKind::Call(func_id, arg_vals), result_ty.clone());
        (val, result_ty)
    }

    fn translate_loc_exp(
        &self,
        loc_exp: &silver::LocAccess,
        ctx: &mut ExpTranslationContext,
    ) -> (exp::Value, typecheck::Type) {
        match loc_exp.loc.as_ref() {
            silver::ExpKind::FuncApp(func_name, args) => {
                self.translate_func_app((func_name, args), ctx)
            }
            silver::ExpKind::Field(..) => self.translate_exp(&loc_exp.loc, ctx),
            _ => unreachable!(),
        }
    }

    fn translate_acc_exp(
        &self,
        acc_exp: &silver::AccExp,
        ctx: &mut ExpTranslationContext,
    ) -> (exp::Value, typecheck::Type) {
        let (loc_val, _) = self.translate_loc_exp(&acc_exp.acc, ctx);
        let (perm_val, _perm_ty) = self.translate_exp(&acc_exp.perm, ctx);

        // IMPORTANT: Impose constraint that permission must be Real type
        // This will cause Numeric types (like 1/2) to resolve to Real
        let perm_key = ctx.tc.get_var_key(&perm_val);
        ctx.tc.impose(perm_key.concretizes_explicit(typecheck::Type::Real))
            .expect("Failed to impose Real constraint on permission");

        // Add to impures list
        ctx.impures.push(exp::Acc {
            loc: loc_val.clone(),
            perm: perm_val,
        });

        // acc() expressions evaluate to true (unit/bool) in the pure context
        (
            exp::Value::Const(exp::Literal::Bool(true)),
            typecheck::Type::Bool,
        )
    }

    fn translate_binop(&self, op: &silver::BinOp) -> exp::BinOp {
        match op {
            silver::BinOp::Plus => exp::BinOp::Plus,
            silver::BinOp::Minus => exp::BinOp::Minus,
            silver::BinOp::Mult => exp::BinOp::Mult,
            silver::BinOp::Div => exp::BinOp::Div,
            silver::BinOp::Mod => exp::BinOp::Mod,
            silver::BinOp::Eq => exp::BinOp::Eq,
            silver::BinOp::Neq => exp::BinOp::Neq,
            silver::BinOp::Lt => exp::BinOp::Lt,
            silver::BinOp::Le => exp::BinOp::Le,
            silver::BinOp::Gt => exp::BinOp::Gt,
            silver::BinOp::Ge => exp::BinOp::Ge,
            _ => unimplemented!("BinOp translation: {:?}", op),
        }
    }

    fn translate_unop(&self, op: &silver::UnOp) -> exp::UnOp {
        match op {
            silver::UnOp::Not => exp::UnOp::Not,
            silver::UnOp::Neg => exp::UnOp::Minus,
            _ => unimplemented!("UnOp translation: {:?}", op),
        }
    }

    /// Translate a complete expression with predefined locals (e.g., for predicate bodies)
    fn translate_complete_exp_with_locals<'a>(
        &self,
        silver_exp: &silver::Exp,
        params: impl IntoIterator<Item = &'a silver::ArgOrType>,
    ) -> exp::Exp {
        // Convert ArgOrType to (IdnDecl, Type) pairs
        let locals = params.into_iter().filter_map(|arg| {
            match arg {
                silver::ArgOrType::Arg(typed) => {
                    let vmir_ty = self.translate_type(&typed.ty);
                    Some((&typed.idn, vmir_ty))
                },
                silver::ArgOrType::Type(_) => None, // Skip type-only parameters
            }
        });
        
        let mut ctx = ExpTranslationContext::new(self, locals);

        let (result, _ty) = self.translate_exp(silver_exp, &mut ctx);
        ctx.finalize(result)
    }

    fn translate_method(&mut self, method: &silver::Method) {
        let sig = &method.signature;
        let ident = sig.name.0 .0.as_str();

        let method_member_id = self
            .interner
            .get(ident)
            .expect("Name should be pre-interned");

        let args: Vec<_> = sig
            .args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();

        let rets: Vec<_> = sig
            .ret
            .iter()
            .map(|ret| self.translate_type(ret.ty()))
            .collect();

        let vmir_method = vmir::Method {
            name: method_member_id,
            signature: vmir::MethSig { args, rets },
            contract: self.translate_method_contract(&method.contract, &method.signature),
            body: None, // TODO: translate method body
        };

        assert!(
            self.globals[method_member_id].is_none(),
            "Declaration at index {} already exists",
            method_member_id.into_usize()
        );
        self.globals[method_member_id] = Some(vmir::Declaration::Method(vmir_method));
    }

    fn translate_function(&mut self, function: &silver::Function) {
        // Functions translate directly - just signatures for now, bodies later
        let sig = &function.signature;
        let contract = &function.contract;
        let ident = sig.name.0 .0.as_str();

        let func_member_id = self
            .interner
            .get(ident)
            .expect("Name should be pre-interned");

        let args: Vec<_> = sig
            .args
            .iter()
            .map(|arg| self.translate_type(arg.ty()))
            .collect();
        let ret = self.translate_type(sig.ret[0].ty());

        let func = vmir::Function {
            name: func_member_id,
            signature: vmir::FuncSig { args, ret },
            contract: self.translate_function_contract(contract, sig),
            body: None, // TODO: translate function body
        };

        assert!(
            self.globals[func_member_id].is_none(),
            "Declaration at index {} already exists",
            func_member_id.into_usize()
        );
        self.globals[func_member_id] = Some(vmir::Declaration::Function(func));
    }

    fn translate_function_contract(
        &self,
        contract: &silver::Contract,
        signature: &silver::Signature,
    ) -> vmir::FuncContract {
        let requires = contract
            .precondition
            .as_ref()
            .map(|pre| self.translate_complete_exp_with_locals(&pre.exp, &signature.args));

        let ensures = contract
            .postcondition
            .as_ref()
            .map(|post| self.translate_complete_exp_with_locals(&post.exp, &signature.args));

        vmir::FuncContract { requires, ensures }
    }

    fn translate_method_contract(
        &self,
        contract: &silver::Contract,
        signature: &silver::Signature,
    ) -> vmir::MethContract {
        let requires = contract
            .precondition
            .as_ref()
            .map(|pre| self.translate_complete_exp_with_locals(&pre.exp, &signature.args));

        let ensures_locals = signature.args.iter().chain(signature.ret.iter());
        let ensures = contract
            .postcondition
            .as_ref()
            .map(|post| self.translate_complete_exp_with_locals(&post.exp, ensures_locals));

        vmir::MethContract { requires, ensures }
    }

    // fn translate_heap_exp_to_contract(
    //     &self,
    //     heap_exp: &silver::HeapExp,
    //     acc_expr: &mut AccExpr,
    //     signature: &silver::Signature,
    // ) {
    //     // Extract acc(...) expressions from the heap expression
    //     let mut acc_exprs = Vec::new();
    //     self.extract_acc_clauses(&heap_exp.exp, &mut acc_exprs, signature);
    //     *acc_expr = AccExpr::SepConj(acc_exprs);
    // }
    //
    // fn extract_acc_clauses(
    //     &self,
    //     exp: &silver::Exp,
    //     acc_exprs: &mut Vec<AccExpr>,
    //     signature: &silver::Signature,
    // ) {
    //     match dbg!(&**exp) {
    //         silver::ExpKind::Acc(acc_exp) => {
    //             // Found an acc expression, convert it to an AccExpr
    //             if let Some(acc) = self.translate_acc_to_expr(acc_exp, signature) {
    //                 acc_exprs.push(acc);
    //             }
    //         }
    //         silver::ExpKind::BinOp(op, left, right) => {
    //             // For && (And), recursively extract from both sides
    //             if matches!(op, silver::BinOp::And) {
    //                 self.extract_acc_clauses(left, acc_exprs, signature);
    //                 self.extract_acc_clauses(right, acc_exprs, signature);
    //             }
    //         }
    //         _ => {
    //             // Other expression types - skip for now
    //         }
    //     }
    // }
    //
    // fn translate_acc_to_expr(
    //     &self,
    //     acc_exp: &silver::AccExp,
    //     signature: &silver::Signature,
    // ) -> Option<AccExpr> {
    //     // acc_exp.acc is a LocAccess which contains the location
    //     // For now, we only handle field accesses: acc(x.f)
    //     match &*acc_exp.acc.loc {
    //         silver::ExpKind::Field(base, field) => {
    //             // In VMIR, field access x.f becomes a function call f_(x)
    //             // which returns an address &T
    //             let base_expr = self.translate_exp_for_contract(base, signature);
    //
    //             // Create a resource expression for the field call
    //             let rsrc_expr =
    //                 RsrcExpr::Call(vmir::Ident(format!("{}_", field.0)), vec![base_expr]);
    //
    //             // Create a permission (write permission for now)
    //             let perm_expr = PermExpr::Const(BigRational::new(1.into(), 1.into()));
    //
    //             Some(AccExpr::Access(rsrc_expr, perm_expr))
    //         }
    //         _ => None,
    //     }
    // }
    //
    // fn translate_exp_for_contract(
    //     &self,
    //     exp: &silver::Exp,
    //     _signature: &silver::Signature,
    // ) -> vmir::expr::Expr {
    //     match &**exp {
    //         silver::ExpKind::Ident(ident) => {
    //             // Look up in signature to see if it's a parameter
    //             // For now, just use Named
    //             vmir::expr::Expr::Ref(vmir::expr::RefExpr::Named(vmir::Ident(ident.0.clone())))
    //         }
    //         _ => {
    //             // Other cases - placeholder for now
    //             vmir::expr::Expr::Ref(vmir::expr::RefExpr::Named(vmir::Ident(
    //                 "unknown".to_string(),
    //             )))
    //         }
    //     }
    // }
}

impl<'a> silver::walk::AstWalker<'a> for VmirTranslator {
    fn walk_method(&mut self, method: &'a silver::Method) {
        self.translate_method(method);
        method.walk_children(self);
    }

    fn walk_field(&mut self, field: &'a silver::Field) {
        self.translate_field(field);
        field.walk_children(self);
    }

    fn walk_predicate(&mut self, pred: &'a silver::Predicate) {
        self.translate_predicate(pred);
        pred.walk_children(self);
    }

    fn walk_function(&mut self, func: &'a silver::Function) {
        self.translate_function(func);
        func.walk_children(self);
    }
}
