//! Run the full pipeline (parse → typecheck → translate → verify) on a file.

use std::path::Path;

use crate::silver::{
    GlobalsCollector, IdentCollector, inline_macros, disambiguate, typecheck_program,
    walk::AstWalkable,
};
use crate::{silver_parser, translate, verify, vmir};

#[derive(Debug)]
pub enum PipelineError {
    Io(std::io::Error),
    Parse(String),
    Typecheck(String),
    Translate(String),
    Analyze(String),
}

impl std::fmt::Display for PipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "IO: {e}"),
            Self::Parse(e) => write!(f, "parse: {e}"),
            Self::Typecheck(e) => write!(f, "typecheck: {e}"),
            Self::Translate(e) => write!(f, "translate: {e}"),
            Self::Analyze(e) => write!(f, "analyze: {e}"),
        }
    }
}

/// Run the full pipeline on a `.vpr` file. Returns per-method results on
/// success, or a `PipelineError` if any pre-verification stage fails.
pub fn run_file(path: &Path) -> Result<Vec<verify::MethodResult>, PipelineError> {
    let input = std::fs::read_to_string(path).map_err(PipelineError::Io)?;

    let mut program = silver_parser::sil_program(&input)
        .map_err(|e| PipelineError::Parse(e.to_string()))?;

    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();

    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector
        .finalize()
        .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?;

    disambiguate(&mut program, &interner, &globals)
        .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?;
    inline_macros(&mut program, &interner)
        .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?;

    let typed = typecheck_program(&mut program, &interner, &globals)
        .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?;

    let vmir = translate::translate(&typed, &interner, &globals)
        .map_err(|e| PipelineError::Translate(format!("{e:?}")))?;

    let analyzed =
        vmir::analyze(vmir).map_err(|e| PipelineError::Analyze(e.to_string()))?;

    Ok(verify::verify(&analyzed))
}
