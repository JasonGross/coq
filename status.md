# Go Extraction Backend — Implementation Status

## Progress

| Step | Description | Status |
|------|------------|--------|
| 1 | Create `go.mli` interface | Done |
| 2 | Create `go.ml` backend | Done |
| 3 | Wire into `table.ml` + `table.mli` (add `Go` to `lang` type) | Done |
| 4 | Wire into `extract_env.ml` (add `Go` to `descr`) | Done |
| 5 | Wire into `g_extraction.mlg` (grammar + printer) | Done |
| 6 | Wire into `common.ml` (add `Go` case to `pp_global_with_key`) | Done |
| 7 | Build and fix compilation errors | Done |
| 8 | Test Go extraction with various Rocq programs | Done |
| 9 | Verify extracted Go code compiles and runs correctly | Done |
| 10 | Add test to test-suite/output/ | Done |
| 11 | Verify existing extraction tests still pass | Done |

## Files Created

- `plugins/extraction/go.mli` — interface exporting `go_descr`
- `plugins/extraction/go.ml` — full Go backend (~500 lines)
- `test-suite/output/extraction_go.v` — test file for Go extraction
- `test-suite/output/extraction_go.out` — expected output for Go extraction test

## Files Modified

- `plugins/extraction/table.ml` — added `Go` to `lang` variant
- `plugins/extraction/table.mli` — added `Go` to `lang` variant
- `plugins/extraction/extract_env.ml` — added `Go -> Go.go_descr` to dispatcher
- `plugins/extraction/g_extraction.mlg` — added `Go` to printer and grammar
- `plugins/extraction/common.ml` — added `Go` case to name qualification

## Go Backend Features Implemented

- **Keywords**: All Go reserved words and built-in identifiers
- **Types**: `any` for type variables/unknowns, `func(a) b` for arrows, named types for globals
- **Inductive types**:
  - Standard sum types → interface + concrete structs with marker methods
  - Records → structs with FieldN fields
  - Singletons → type aliases
  - Coinductive → thunk-wrapping structs
  - Logical → comment stubs
- **Expressions**: lambda, application (Go-style `f(a, b)`), let-in (IIFE with proper newlines), global refs, constructors, tuples, case/match (type switch), fixpoints, exceptions (panic), dummy, magic, uint64, float64, strings, parray stub
- **Pattern matching**: type switch; omits variable binding when no branch uses fields
- **Recursion**: single (local IIFE), mutual (var block + init)
- **Preamble**: `package` declaration, conditional `import "unsafe"`, `dummy__`, `magic__`
- **Module flattening**: non-functor modules flattened, functors dropped with comment

## Testing

- Extracted Go code compiles and runs correctly with `go run`
- Verified: nat addition/multiplication, bool operations, list map, mutual recursion
- Test suite test passes: `test-suite/output/extraction_go.v`
- All existing extraction tests still pass (Extraction_ffi, Extraction_infix, Extraction_matchs_2413, extraction_projection, bug_20711, bug_17369, bug_19806)
