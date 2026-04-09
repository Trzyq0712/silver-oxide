# Copilot Instructions for silver-oxide

## Project Overview

**silver-oxide** is a Rust parser and AST (Abstract Syntax Tree) implementation for Silver, Viper's intermediate verification language. The project includes:

- **Parser** (`src/silver/peg.rs`): PEG-based parser for Silver syntax (prioritizes legibility over performance)
- **AST** (`src/silver/ast.rs`): Type definitions for Silver program structures
- **Translator** (`src/translate/`): Multi-pass translation to VMIR (Viper Mid-level IR), including:
  - Name Resolution: Collect and resolve symbol definitions
  - Type Checking: Infer and validate types (currently inline; future refactoring planned)
  - Expression Translation: Convert Silver expressions to VMIR
- **VMIR** (`src/vmir/`): Intermediate representation with display/printing capabilities
- **Binaries**: Parser, Translator, and Verifier CLI tools in `src/bin/`

The project is designed for research/thesis work with emphasis on code clarity for AST conformance verification.

## Build, Test, and Lint Commands

### Building
```bash
cargo build              # Debug build
cargo build --release   # Optimized build
cargo build --lib       # Library only
cargo build --bins      # All binaries
```

### Testing
```bash
cargo test --lib                    # Run all library tests
cargo test --lib <test_name>        # Run a single test by name (e.g., test_simple_method_translation)
cargo test --lib -- --nocapture     # Show println! output from tests
```

Current test locations:
- `src/lib.rs`: Integration tests for parsing and translation
- `src/silver/peg.rs`: Parser tests (precedence_test)
- `src/translate/name_resolution.rs`: Name resolution tests
- Example files: `test.sil`, `test2.sil`, `test3.sil`, `test_method.sil`, `test_simple_method.sil`

### Linting & Formatting
```bash
cargo clippy                # Run clippy linter
cargo clippy --fix          # Auto-fix issues where possible
cargo fmt                   # Format code (uses rustfmt)
cargo fmt -- --check        # Check formatting without modifying
```

## Architecture & Modules

### Core Pipeline: Silver → VMIR

1. **Parsing** (`src/silver/peg.rs`)
   - Input: Silver source code (`.sil` files)
   - Output: `Program` AST
   - Uses `peg` crate for PEG parser combinators
   - Grammar includes: identifiers, types, expressions, statements, annotations

2. **Name Resolution** (`src/translate/name_resolution.rs`)
   - Input: AST from parser
   - Traverses AST and collects all declarations (methods, fields, variables)
   - Builds symbol table (using `lasso` for string interning)
   - Output: `NameCollector` context for later translation phases

3. **Type Checking** (`src/translate/typecheck.rs`)
   - Currently inline during expression translation
   - Uses `rusttyc` type inference library
   - Future: planned refactor to separate type checking pass (see `src/translate/mod.rs` comments)

4. **Expression Translation** (`src/translate/exp.rs`)
   - Converts Silver expressions to VMIR IR
   - Uses `ExpTranslationContext` to track local state
   - Leverages `AstWalkable` trait for AST traversal

5. **VMIR Output** (`src/vmir/`)
   - `ast.rs`: VMIR AST definitions
   - `display.rs`: Pretty-printing with indentation
   - `pure.rs`: Pure VMIR values
   - `impure.rs`: Impure (stateful) operations

### Key Types & Traits

- **`Ident`** (`src/silver/ast.rs`): Wrapper around String for identifiers
- **`IdnDecl`**: Declaration with identifier
- **`AstWalkable`** (`src/silver/walk.rs`): Trait for generic AST traversal
- **`TiVec<K, V>`** (`typed-index-collections`): Type-safe indexed vectors using newtype indices (used for VMIR member/method IDs)

### AST Representation

- Heavy use of **newtype wrappers** (e.g., `Ident(String)`) for type safety
- `derive_more` crate for convenient Display/From implementations
- `IndexMap` used for ordered key-value storage

## Key Conventions

### Code Organization
- **Module structure mirrors pipeline**: `silver/` (parsing) → `translate/` (translation) → `vmir/` (output)
- Binary CLI tools in `src/bin/` are separate from library code
- `util.rs` and module-specific `util.rs` files for shared helpers

### AST and Type Patterns
- **Newtype wrappers** for semantic clarity: `Ident(String)`, `IdnDecl`, etc.
- **Indexed types**: Use `TiVec<MemberId, Type>` instead of plain vectors for compile-time safety
- **Derive macros**: Most AST nodes use `#[derive(...)]` with `derive_more` for Display/Debug

### Parser Conventions (`src/silver/peg.rs`)
- PEG rule functions return `Result` types
- Helper rules (underscore prefix like `___`, `__`, `_`): whitespace and comment handling
- Reserved keywords checked explicitly before identifier parsing
- Comments support: `//` line comments and `/* */` block comments
- Annotations: `@identifier.qualified.name("string_args")`

### Translation Phase Conventions
- **String interning**: Use `Rodeo<K>` (from `lasso`) for efficient identifier storage
- **Name resolution**: `NameCollector` walks AST once to gather all symbols
- **Type context**: `ExpTranslationContext` tracks environment during expression translation
- **Error handling**: Use `Result` types; TODO comments indicate incomplete features

### VMIR Output
- Pretty-printing respects indentation levels via `Display` trait
- VMIR nodes are separate from Silver AST (not just wrapped)

### Variable Naming
- **Parser contexts**: Suffix with `_context` or just named `ctx`
- **Temporary collections**: `names`, `decls` for intermediate AST processing
- **Type checkers/collectors**: Explicitly named `NameCollector`, `TypeChecker`, etc.

### Future TODOs
- Separate type checking into a distinct pass (currently inline during translation)
- Add higher-performance parser alternative (maintain legible PEG as baseline)
- Verify translation correctness against Viper reference implementation

## Debugging Notes

- **Parser issues**: Enable stdout with `cargo test --lib -- --nocapture` to see println! output
- **Translation failures**: Check `src/translate/typecheck.rs` for type inference errors; enable verbose output in `ExpTranslationContext`
- **Name resolution errors**: Review `NameCollector` symbol table collection in `src/translate/name_resolution.rs`

## Dependencies

Key crates:
- **peg** (0.8.5): Parser generator
- **lasso** (0.7.3): String interning
- **rusttyc** (0.5.0): Type checking
- **typed-index-collections** (3.5.0): Type-safe indexed vectors
- **z3** (0.19.15): SMT solver (integrated for verification)
- **egg** (0.11.0): E-graph library (may be used for optimization)
- **derive_more** (0.99): Convenience derives
- **num** (0.4.3): Big integers for numeric literals
