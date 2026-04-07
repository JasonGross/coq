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

## Files Created

- `plugins/extraction/go.mli` — interface exporting `go_descr`
- `plugins/extraction/go.ml` — full Go backend (~480 lines)

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
  - Records → structs with named fields
  - Singletons → type aliases
  - Coinductive → thunk-wrapping structs
  - Logical → comment stubs
- **Expressions**: lambda, application, let-in (IIFE), global refs, constructors, tuples, case/match (type switch), fixpoints, exceptions (panic), dummy, magic, uint64, float64, strings, parray stub
- **Pattern matching**: type switch with `Pusual`, `Pcons`, `Ptuple`, `Pwild`, `Prel`
- **Recursion**: single (local IIFE), mutual (var block + init)
- **Preamble**: `package` declaration, conditional `import "unsafe"`, `dummy__`, `magic__`
- **Module flattening**: non-functor modules flattened, functors dropped with comment

## Notes

- Build succeeds cleanly with `dune build plugins/extraction` (no warnings)
- Pre-existing unrelated error in full `dune build` (rocq-core empty package)
- No dune changes needed (auto-discovery picks up go.ml)
