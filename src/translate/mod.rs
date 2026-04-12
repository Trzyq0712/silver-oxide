use crate::silver::walk::AstWalkable;
use crate::translate::method::MethodTranslCtxt;
use crate::translate::name_resolution::DeclKind;
use crate::vmir;
use crate::{silver, translate::heap_exp::HeapExpTranslCtxt};
use lasso::{Key, Rodeo};
use rusttyc::{TcErr, TcKey, TcVar, TypeChecker};
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

pub mod heap_exp;
pub mod method;
pub mod name_resolution;
pub mod signatures;
pub mod typecheck;
pub use name_resolution::{IdentifierError, NameCollector};
pub use signatures::SignatureContext;

#[derive(Debug)]
pub struct VmirTranslator {
    globals: TiVec<vmir::MemberId, Option<vmir::Declaration>>,
    interner: Rodeo<vmir::MemberId>,
    name_kinds: TiVec<vmir::MemberId, DeclKind>,
    signatures: SignatureContext,
}

impl VmirTranslator {
    /// Create a new translator with a pre-populated interner from name collection.
    pub fn new(
        interner: Rodeo<vmir::MemberId>,
        name_kinds: TiVec<vmir::MemberId, DeclKind>,
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
        // 1. function pr(x: Ref, i: Int): &pr@snap
        //    An abstract function that maps the predicate arguments to a snapshot address
        //    When dereferenced (* operator), evaluates to the snapshot
        // 2. resource pr@heap(x: Ref, i: Int)
        //    { body }
        //    Effectively can be thought of as a macro that will auto-expand in a requires or
        //    ensures clause
        // 3. function pr@to_snap(x: Ref, i: Int): pr@snap
        //      requires pr@heap(x, i)
        //    { pr@snap(...) }
        //    A function to construct the snapshot directly from the heap (from the unfolded predicate)
        // 4. Is body present:
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
            Some(ref _body) => {
                // TODO: When translating the predicate body:
                // 1. Create an ExpTranslationContext with predicate parameters as locals
                // 2. Use translate_complete_exp to translate body.0 (the Exp)
                // 3. Extract impures (acc expressions) to build the ADT snapshot
                //
                // Example:
                // let vmir::exp = self.translate_complete_exp(&body.0);
                // // vmir::exp.impures contains all acc(...) expressions
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
            body: None,
            // predicate
            //     .body
            //     .as_ref()
            //     .map(|body| self.translate_impure_exp(&body.0.exp, &sig.args, &vmir::Type::Bool)),
        };

        assert!(
            self.globals[resource_id].is_none(),
            "Declaration at index {} already exists",
            resource_id.into_usize()
        );
        self.globals[resource_id] = Some(vmir::Declaration::Resource(resource));
    }

    // /// Translate a complete expression with predefined locals (e.g., for predicate bodies)
    // fn translate_impure_exp<'a>(
    //     &self,
    //     exp: &silver::ExpKind,
    //     env: impl IntoIterator<Item = &'a silver::ArgOrType>,
    //     ty: &vmir::Type,
    // ) -> vmir::HeapExp {
    //     // Convert ArgOrType to (IdnDecl, Type) pairs
    //     let locals = env.into_iter().filter_map(|arg| {
    //         match arg {
    //             silver::ArgOrType::Arg(typed) => {
    //                 let vmir_ty = self.translate_type(&typed.ty);
    //                 Some((&typed.idn, vmir_ty))
    //             }
    //             silver::ArgOrType::Type(_) => None, // Skip type-only parameters
    //         }
    //     });
    //
    //     let ctx = HeapExpTranslCtxt::new(self, locals);
    //
    //     ctx.translate_exp(exp)
    // }

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

        // TODO: Temporarily disabled method body translation
        // let body = method
        //     .body
        //     .as_ref()
        //     .map(|body_block| self.translate_method_body(body_block, &method.signature));
        //
        self.translate_method_contract(ident, &method.contract, &method.signature);

        let vmir_method = vmir::Method {
            name: method_member_id,
            signature: vmir::MethSig { args, rets },
            body: vmir::StmtBlock(vec![]),
        };

        if let Some(body) = &method.body {
            let mut trans_ctxt = MethodTranslCtxt::new(self, &method.signature);

            for stmt in &body.0 {
                trans_ctxt.translate_statement(stmt);
            }

            let _method = trans_ctxt.finalize();
            let vmir_display = vmir::display::VmirDisplay::new(&_method, &self.interner);
            println!("Translated method body for {}:\n{}", ident, vmir_display);
        }

        self.add_decl(method_member_id, vmir::Declaration::Method(vmir_method));
    }

    fn add_decl(&mut self, memid: vmir::MemberId, decl: vmir::Declaration) {
        assert!(
            self.globals[memid].is_none(),
            "Declaration at index {} already exists",
            memid.into_usize()
        );
        self.globals[memid] = Some(decl);
    }

    /* Temporarily disabled method body translation
        /// Translate a method body, collecting variable declarations and translating statements
        fn translate_method_body(
            &self,
            body: &silver::StmtBlock,
            signature: &silver::Signature,
        ) -> vmir::StmtBlock {
            // Prepare parameters (both args and return values) for MethodTranslationContext
            let params = signature
                .args
                .iter()
                .chain(signature.ret.iter())
                .filter_map(|arg| match arg {
                    silver::ArgOrType::Arg(decl_typed) => {
                        Some((&decl_typed.idn, self.translate_type(&decl_typed.ty)))
                    }
                    silver::ArgOrType::Type(_) => None,
                });

            let mut ctx = MethodTranslationContext::new(self, params);

            // Phase 1: Collect all variable declarations
            self.collect_var_decls(&body.0, &mut ctx);

            // Phase 2: Translate statements
            for stmt in &body.0 {
                self.translate_statement(stmt, &mut ctx);
            }

            vmir::StmtBlock(ctx.statements)
        }

        /// Recursively collect variable declarations from statements
        fn collect_var_decls<'c>(
            &self,
            stmts: &'c [silver::Statement],
            ctx: &mut MethodTranslationContext<'_, 'c>,
        ) {
            for stmt in stmts {
                match stmt {
                    silver::Statement::Var(decls, _init) => {
                        // Allocate local for each declared variable
                        for decl in decls {
                            let name = decl.idn.0 .0.as_str();
                            let ty = typecheck::TcType::from_vmir_type(&self.translate_type(&decl.ty));
                            ctx.allocate_local(name, ty);
                        }
                    }
                    silver::Statement::Block(block) => {
                        self.collect_var_decls(&block.0, ctx);
                    }
                    silver::Statement::If(_cond, then_block, else_block) => {
                        self.collect_var_decls(&then_block.0, ctx);
                        if let Some(else_block) = else_block {
                            self.collect_var_decls(&else_block.0, ctx);
                        }
                    }
                    silver::Statement::While(_cond, _inv, _decr, body) => {
                        self.collect_var_decls(&body.0, ctx);
                    }
                    _ => {
                        // Other statements don't contain variable declarations
                    }
                }
            }
        }

        /// Translate a single statement
        fn translate_statement(&self, stmt: &silver::Statement, ctx: &mut MethodTranslationContext) {
            match stmt {
                silver::Statement::Assign(lhs_vec, rhs) => {
                    self.translate_assign(lhs_vec, rhs, ctx);
                }
                silver::Statement::Var(decls, init) => {
                    // Variable declarations are already collected
                    // Only handle initialization if present
                    if let Some(init_rhs) = init {
                        // Generate assignment statement(s) for initialized variables
                        // Silver allows: var x: Int, y: Int := expr1, expr2
                        // We translate this to separate assignments
                        let lhs_vec: Vec<_> = decls
                            .iter()
                            .map(|decl| {
                                // Create an Ident expression for the declared variable
                                Box::new(silver::ExpKind::Ident(decl.idn.0.clone()))
                            })
                            .collect();

                        // Translate as a regular assignment
                        self.translate_assign(&lhs_vec, init_rhs, ctx);
                    }
                }
                _ => {
                    // For now, we only support Assign and Var
                    // Other statements will be added later
                    panic!("Statement not yet supported: {:?}", stmt);
                }
            }
        }

        /// Translate an assignment statement
        fn translate_assign(
            &self,
            lhs_vec: &[silver::Exp],
            rhs: &silver::AssignRhs,
            ctx: &mut MethodTranslationContext,
        ) {
            match rhs {
                silver::AssignRhs::Exp(rhs_exp) => {
                    // Simple assignment: lhs := rhs_exp
                    assert_eq!(lhs_vec.len(), 1, "Multiple LHS not supported yet");
                    let lhs = &lhs_vec[0];

                    // Translate RHS expression
                    let rhs_vmir = self.translate_stmt_exp(rhs_exp, ctx);

                    // Determine assignment target
                    let target = self.translate_assign_target(lhs, ctx);

                    // Add assignment statement
                    ctx.add_statement(vmir::Statement::Assign(target, rhs_vmir));
                }
                silver::AssignRhs::Call(method_name, args) => {
                    // Method call: lhs := m(args)
                    // Get method ID
                    let method_id = self
                        .interner
                        .get(&method_name.0)
                        .expect("Method name should be interned");

                    // Translate arguments
                    let arg_exps: Vec<_> = args
                        .iter()
                        .map(|arg| self.translate_stmt_exp(arg, ctx))
                        .collect();

                    // Translate LHS to locals/temps
                    let lhs_locals: Vec<_> = lhs_vec
                        .iter()
                        .map(|lhs_exp| self.translate_method_call_target(lhs_exp, ctx))
                        .collect();

                    // Add method call statement
                    ctx.add_statement(vmir::Statement::MethodCall(lhs_locals, method_id, arg_exps));
                }
                silver::AssignRhs::New(_) => {
                    // TODO: Handle "new" statements
                    panic!("'new' statement not yet supported");
                }
            }
        }

        /// Translate an expression in statement context (evaluate to expression with SSA)
        fn translate_stmt_exp(
            &self,
            exp: &silver::Exp,
            ctx: &MethodTranslationContext,
        ) -> vmir::vmir::exp::Exp {
            // Reuse ExpTranslationContext for expression translation
            // We need to create a temporary collection that owns the IdnDecl instances
            let locals_vec: Vec<(silver::IdnDecl, vmir::Type)> = ctx
                .locals
                .iter()
                .map(|(name, (_idx, ty))| {
                    let decl = silver::IdnDecl(silver::Ident((*name).to_string()));
                    let vmir_ty = ty.to_vmir_type();
                    (decl, vmir_ty)
                })
                .collect();

            // Now create the iterator with references
            let locals_for_exp = locals_vec.iter().map(|(decl, ty)| (decl, ty.clone()));

            let mut exp_ctx = ExpTranslationContext::new(self, locals_for_exp);
            let (result, _ty) = self.translate_exp(exp, &mut exp_ctx);
            exp_ctx.finalize(result)
        }

        /// Translate an LHS expression to an AssignTarget
        fn translate_assign_target(
            &self,
            lhs: &silver::Exp,
            ctx: &mut MethodTranslationContext,
        ) -> vmir::AssignTarget {
            match lhs.as_ref() {
                silver::ExpKind::Ident(name) => {
                    // Simple variable assignment
                    let (idx, _ty) = ctx
                        .locals
                        .get(name.0.as_str())
                        .expect("Variable not found in locals");
                    vmir::AssignTarget::Local(*idx)
                }
                silver::ExpKind::Field(_receiver, _field) => {
                    // Field assignment: x.f := value
                    // Translate to: *temp := value where temp = field_addr(x)

                    // Get field address as an expression
                    let field_addr_exp = self.translate_stmt_exp(lhs, ctx);

                    // The result of the expression should be a temporary holding the address
                    // Extract the temp from the expression result
                    match field_addr_exp.res {
                        vmir::vmir::exp::Value::Temp(temp_idx) => vmir::AssignTarget::Deref(temp_idx),
                        _ => panic!("Field access should produce a temporary"),
                    }
                }
                _ => panic!("Unsupported LHS expression: {:?}", lhs),
            }
        }

        /// Translate an LHS expression for method call (must be a local or temp)
        fn translate_method_call_target(
            &self,
            lhs: &silver::Exp,
            ctx: &mut MethodTranslationContext,
        ) -> vmir::Local {
            match lhs.as_ref() {
                silver::ExpKind::Ident(name) => {
                    // Variable as method call target
                    let (idx, _ty) = ctx
                        .locals
                        .get(name.0.as_str())
                        .expect("Variable not found in locals");
                    vmir::Local::Local(*idx)
                }
                _ => {
                    // Complex expression - evaluate to a temporary first
                    let exp_vmir = self.translate_stmt_exp(lhs, ctx);
                    match exp_vmir.res {
                        vmir::vmir::exp::Value::Temp(temp_idx) => vmir::Local::Temp(temp_idx),
                        vmir::vmir::exp::Value::Local(local_idx) => vmir::Local::Local(local_idx),
                        _ => panic!("Method call target must be a local or temp"),
                    }
                }
            }
        }
    */

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
            contract: vmir::FuncContract::empty(), // TODO: translate function contract
            body: None,                            // TODO: translate function body
        };

        assert!(
            self.globals[func_member_id].is_none(),
            "Declaration at index {} already exists",
            func_member_id.into_usize()
        );
        self.globals[func_member_id] = Some(vmir::Declaration::Function(func));
    }

    // fn translate_function_contract(
    //     &self,
    //     contract: &silver::Contract,
    //     signature: &silver::Signature,
    // ) -> vmir::FuncContract {
    //     // Build requires input signature: [heap, ...args]
    //     let mut requires_inputs = vec![vmir::Type::Heap];
    //     for arg in &signature.args {
    //         if let silver::ArgOrType::Arg(typed) = arg {
    //             requires_inputs.push(self.translate_type(&typed.ty));
    //         }
    //     }
    //
    //     let requires = contract
    //         .precondition
    //         .as_ref()
    //         .map(|pre| self.translate_impure_exp(&pre.exp, &signature.args, &vmir::Type::Bool));
    //
    //     // Build ensures input signature: [heap, old_heap, ...args]
    //     let mut ensures_inputs = vec![vmir::Type::Heap, vmir::Type::Heap];
    //     for arg in &signature.args {
    //         if let silver::ArgOrType::Arg(typed) = arg {
    //             ensures_inputs.push(self.translate_type(&typed.ty));
    //         }
    //     }
    //
    //     let ensures = contract
    //         .postcondition
    //         .as_ref()
    //         .map(|post| self.translate_impure_exp(&post.exp, &signature.args, &vmir::Type::Bool));
    //
    //     vmir::FuncContract::with_inputs(requires, ensures, requires_inputs, ensures_inputs)
    // }

    fn translate_method_contract(
        &mut self,
        method: &str,
        contract: &silver::Contract,
        signature: &silver::Signature,
    ) {
        const TRUE_EXP: silver::ExpKind = silver::ExpKind::Const(silver::ConstKind::Bool(true));

        let memid = self.interner.get(method).unwrap();

        let requires = {
            let ctxt = HeapExpTranslCtxt::new_for_requires(
                self,
                memid,
                signature.args.iter().map(|a| a.idn().unwrap()),
            );
            ctxt.translate_exp(
                contract
                    .precondition
                    .as_ref()
                    .map_or(&TRUE_EXP, |pre| &pre.exp),
            )
        };
        let ensures = {
            let ctxt = HeapExpTranslCtxt::new_for_ensures(
                self,
                memid,
                signature.args.iter().map(|a| a.idn().unwrap()),
                signature.ret.iter().filter_map(|r| r.idn()),
            );
            ctxt.translate_exp(
                contract
                    .postcondition
                    .as_ref()
                    .map_or(&TRUE_EXP, |post| &post.exp),
            )
        };

        let requires_memid = self.interner.get(format!("{method}@requires")).unwrap();
        self.add_decl(requires_memid, vmir::Declaration::HeapExp(requires));
        let ensures_memid = self.interner.get(format!("{method}@ensures")).unwrap();
        self.add_decl(ensures_memid, vmir::Declaration::HeapExp(ensures));
    }
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
