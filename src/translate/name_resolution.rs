use crate::silver;
use crate::silver::walk::AstWalker;
use lasso::{Key, Rodeo};
use typed_index_collections::TiVec;

/// A pass that collects and interns all declaration names from the Silver AST.
/// This ensures no duplicate names and provides a mapping from names to their IDs.
pub struct NameCollector<K> {
    interner: Rodeo<K>,
    /// Maps interned keys to their declaration kinds for error reporting
    name_locations: TiVec<K, NameLocation>,
    /// Tracks if we encountered any errors during collection
    errors: Vec<IdentifierError>,
}

#[derive(Debug, Clone)]
pub struct NameLocation {
    pub kind: DeclKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Field,
    Function,
    Predicate,
    Method,
    HeapExp,
    Domain,
    DomainFunction,
    Adt,
    AdtConstructor,
}

impl<K> NameCollector<K>
where
    K: Key + From<usize> + Into<usize>,
{
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
            name_locations: TiVec::new(),
            errors: Vec::new(),
        }
    }

    /// Collect and intern all names from a Silver program.
    /// Returns an error if there are duplicate declarations.
    pub fn collect(
        mut self,
        program: &silver::Program,
    ) -> Result<(Rodeo<K>, TiVec<K, DeclKind>), Vec<IdentifierError>> {
        use crate::silver::walk::AstWalkable;

        program.walk(&mut self);

        if self.errors.is_empty() {
            let kinds = self
                .name_locations
                .into_iter()
                .map(|loc| loc.kind)
                .collect();
            Ok((self.interner, kinds))
        } else {
            Err(self.errors)
        }
    }

    fn register_name(&mut self, name: &str, kind: DeclKind) {
        // Check if the name already exists
        if let Some(existing_key) = self.interner.get(name) {
            let existing = &self.name_locations[existing_key];
            self.errors.push(IdentifierError::DuplicateName {
                name: name.to_string(),
                first_kind: existing.kind,
                second_kind: kind,
            });
            return;
        }

        let key = self.interner.get_or_intern(name);
        self.name_locations.push(NameLocation { kind });

        // Verify that the key matches the index we just pushed to
        debug_assert_eq!(key.into_usize(), self.name_locations.len() - 1);
    }

    fn interner(&self) -> &Rodeo<K> {
        &self.interner
    }
}

impl<K> Default for NameCollector<K>
where
    K: Key + From<usize> + Into<usize>,
{
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdentifierError {
    DuplicateName {
        name: String,
        first_kind: DeclKind,
        second_kind: DeclKind,
    },
}

impl std::fmt::Display for IdentifierError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IdentifierError::DuplicateName {
                name,
                first_kind,
                second_kind,
            } => {
                write!(
                    f,
                    "Duplicate declaration: '{}' is declared as both {:?} and {:?}",
                    name, first_kind, second_kind
                )
            }
        }
    }
}

impl std::error::Error for IdentifierError {}

// Implement AstWalker to traverse the Silver AST
impl<'a, K> AstWalker<'a> for NameCollector<K>
where
    K: Key + From<usize> + Into<usize>,
{
    fn walk_field(&mut self, field: &'a silver::Field) {
        let name = &field.0.idn.0 .0;
        self.register_name(name, DeclKind::Field);
    }

    fn walk_function(&mut self, func: &'a silver::Function) {
        let name = &func.signature.name.0 .0;
        self.register_name(name, DeclKind::Function);
    }

    fn walk_predicate(&mut self, pred: &'a silver::Predicate) {
        let name = &pred.signature.name.0 .0;
        self.register_name(name, DeclKind::Predicate);

        // TODO: Probably we don't want to generate errors for these names

        // Also register the generated snapshot and resource names
        let snap_name = format!("{}@snap", name);
        let resource_name = format!("{}@heap", name);
        self.register_name(&snap_name, DeclKind::Domain); // or Adt
        self.register_name(&resource_name, DeclKind::Predicate); // resource
    }

    fn walk_method(&mut self, method: &'a silver::Method) {
        let name = &method.signature.name.0 .0;
        self.register_name(name, DeclKind::Method);
    }

    fn walk_domain(&mut self, domain: &'a silver::Domain) {
        let name = &domain.name.0 .0;
        self.register_name(name, DeclKind::Domain);
    }

    fn walk_domain_function(&mut self, func: &'a silver::DomainFunction) {
        let name = &func.signature.name.0 .0;
        self.register_name(name, DeclKind::DomainFunction);
    }

    fn walk_adt(&mut self, adt: &'a silver::Adt) {
        let name = &adt.name.0 .0;
        self.register_name(name, DeclKind::Adt);
    }

    fn walk_adt_constructor(&mut self, ctor: &'a silver::AdtConstructor) {
        let name = &ctor.signature.name.0 .0;
        self.register_name(name, DeclKind::AdtConstructor);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vmir::MemberId;

    #[test]
    fn test_no_duplicates() {
        let program = silver::Program(vec![
            silver::Declaration::Field(silver::Field(silver::IdnDeclTyped {
                idn: silver::IdnDecl(silver::Ident("x".to_string())),
                ty: silver::Type::Int,
            })),
            silver::Declaration::Function(silver::Function {
                signature: silver::Signature {
                    name: silver::IdnDecl(silver::Ident("f".to_string())),
                    args: vec![],
                    ret: vec![],
                },
                contract: silver::Contract {
                    precondition: None,
                    postcondition: None,
                    decreases: vec![],
                },
                body: None,
            }),
        ]);

        let collector = NameCollector::<MemberId>::new();
        let result = collector.collect(&program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_duplicate_names() {
        let program = silver::Program(vec![
            silver::Declaration::Field(silver::Field(silver::IdnDeclTyped {
                idn: silver::IdnDecl(silver::Ident("x".to_string())),
                ty: silver::Type::Int,
            })),
            silver::Declaration::Function(silver::Function {
                signature: silver::Signature {
                    name: silver::IdnDecl(silver::Ident("x".to_string())),
                    args: vec![],
                    ret: vec![],
                },
                contract: silver::Contract {
                    precondition: None,
                    postcondition: None,
                    decreases: vec![],
                },
                body: None,
            }),
        ]);

        let collector = NameCollector::<MemberId>::new();
        let result = collector.collect(&program);
        assert!(result.is_err());
    }
}
