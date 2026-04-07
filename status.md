# Go Extraction Backend — Implementation Status

## Progress — Complete

| Step | Description | Status |
|------|------------|--------|
| 1 | Create `go.mli` interface | Done |
| 2 | Create `go.ml` backend | Done |
| 3 | Wire into `table.ml` + `table.mli` | Done |
| 4 | Wire into `extract_env.ml` | Done |
| 5 | Wire into `g_extraction.mlg` | Done |
| 6 | Wire into `common.ml` | Done |
| 7 | Build and fix compilation errors | Done |
| 8 | Test Go extraction | Done |
| 9 | Verify extracted Go compiles and runs | Done |
| 10 | Add test-suite tests | Done |
| 11 | Fix edge cases (underscore patterns, multi-arg fixpoints) | Done |
| 12 | Verify all existing extraction tests pass | Done |

## Commits

1. `3b71f8b` — Add Go as a new extraction target language
2. `6ec5c7b` — Fix Go extraction backend and add test suite
3. `dde9638` — Fix Go extraction edge cases and expand test coverage

## Files Created

- `plugins/extraction/go.mli` — interface exporting `go_descr`
- `plugins/extraction/go.ml` — full Go backend (~520 lines)
- `test-suite/output/extraction_go.v` — 13 test cases
- `test-suite/output/extraction_go.out` — expected output

## Files Modified

- `plugins/extraction/table.ml` + `table.mli` — `Go` in `lang` variant
- `plugins/extraction/extract_env.ml` — `Go -> Go.go_descr` dispatcher
- `plugins/extraction/g_extraction.mlg` — `Go` grammar + printer
- `plugins/extraction/common.ml` — `Go` case in name qualification

## Test Coverage

Test suite (`extraction_go.v`) covers:
1. Simple inductive (enum) types
2. Pattern matching on bool
3. Recursive functions (nat addition)
4. Record types
5. Higher-order functions
6. Parametric inductive types (option)
7. Let-in expressions (IIFE)
8. Mutual recursion (even/odd via init)
9. Polymorphic identity
10. Function composition
11. Wildcard/underscore patterns (Nat.eqb)
12. Multi-arg local fixpoints
13. Empty/logical inductive types

Manual Go compilation tests verified:
- nat add/mul: `2+3=5`, `2*3=6`
- bool negb/andb: correct
- list map: `map S [0,1] = [1,2]`
- mutual recursion: `even(4)=true`, `odd(3)=true`
- factorial: `5!=120`
- eqb: `eqb(3,3)=true`, `eqb(3,5)=false`

All 9 existing extraction tests still pass.
