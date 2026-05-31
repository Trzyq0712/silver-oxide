use crate::viper::{Ident, walk::AstWalkerMut};

pub type Interner = lasso::RodeoResolver;

#[derive(Debug, Clone, Default)]
pub struct IdentCollector {
    interner: lasso::Rodeo,
}

impl IdentCollector {
    pub fn finalize(self) -> Interner {
        self.interner.into_resolver()
    }
}

impl AstWalkerMut<'_> for IdentCollector {
    fn walk_mut_ident(&mut self, ident: &mut Ident) {
        if let Ident::Raw(raw) = ident {
            let interned = self.interner.get_or_intern(&raw);
            *ident = Ident::Interned(interned);
        }
    }
}
