use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    UnknownIdent(String),
}

impl fmt::Display for TranslationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TranslationError::Unsupported(what) => write!(f, "unsupported: {what}"),
            TranslationError::UnknownIdent(name) => write!(f, "unknown identifier: {name}"),
        }
    }
}

impl std::error::Error for TranslationError {}
