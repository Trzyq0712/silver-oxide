//! Run the full pipeline (parse → typecheck → translate → verify) on a file.

use std::path::Path;
use std::time::{Duration, Instant};

use crate::viper::{
    GlobalsCollector, IdentCollector, inline_macros, disambiguate, typecheck_program,
    walk::AstWalkable,
};
use crate::{viper_parser, translate, verify, vmir};

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

/// Wall-clock duration of each pipeline phase, in execution order.
#[derive(Debug, Default)]
pub struct PhaseTimings {
    pub phases: Vec<(&'static str, Duration)>,
    pub total: Duration,
}

impl std::fmt::Display for PhaseTimings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (name, dur) in &self.phases {
            writeln!(f, "  {name:<12} {:>10.3?}", dur)?;
        }
        write!(f, "  {:<12} {:>10.3?}", "total", self.total)
    }
}

/// Run the full pipeline on a `.vpr` file. Returns per-method results on
/// success, or a `PipelineError` if any pre-verification stage fails.
pub fn run_file(path: &Path) -> Result<Vec<verify::MethodResult>, PipelineError> {
    run_file_timed(path).map(|(results, _)| results)
}

/// Like [`run_file`] but also returns the [`PhaseTimings`] for each phase.
pub fn run_file_timed(
    path: &Path,
) -> Result<(Vec<verify::MethodResult>, PhaseTimings), PipelineError> {
    let mut timings = PhaseTimings::default();
    let overall = Instant::now();

    // Time a phase, recording its duration under `name`.
    macro_rules! phase {
        ($name:literal, $body:expr) => {{
            let start = Instant::now();
            let out = $body;
            timings.phases.push(($name, start.elapsed()));
            out
        }};
    }

    let input = std::fs::read_to_string(path).map_err(PipelineError::Io)?;

    let mut program = phase!(
        "parse",
        viper_parser::vpr_program(&input).map_err(|e| PipelineError::Parse(e.to_string()))?
    );

    let interner = phase!("idents", {
        let mut ident_collector = IdentCollector::default();
        program.walk_mut(&mut ident_collector);
        ident_collector.finalize()
    });

    let globals = phase!("globals", {
        let mut globals_collector = GlobalsCollector::new(&interner);
        program.walk(&mut globals_collector);
        globals_collector
            .finalize()
            .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?
    });

    phase!(
        "disambiguate",
        disambiguate(&mut program, &interner, &globals)
            .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?
    );

    phase!(
        "macros",
        inline_macros(&mut program, &interner)
            .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?
    );

    let typed = phase!(
        "typecheck",
        typecheck_program(&mut program, &interner, &globals)
            .map_err(|e| PipelineError::Typecheck(format!("{e:?}")))?
    );

    let vmir = phase!(
        "translate",
        translate::translate(&typed, &interner, &globals)
            .map_err(|e| PipelineError::Translate(format!("{e:?}")))?
    );

    let analyzed = phase!(
        "analyze",
        vmir::analyze(vmir).map_err(|e| PipelineError::Analyze(e.to_string()))?
    );

    let results = phase!("verify", verify::verify(&analyzed));

    timings.total = overall.elapsed();
    Ok((results, timings))
}
