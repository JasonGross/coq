#!/usr/bin/env bash

# Regression test for Bug 3: an unrealised Parameter (axiom of non-Type
# sort) was being extracted as `func Foo() any { return panic(...) }`,
# which Go rejects because panic returns no value. The fix emits a bare
# `panic(...)` statement at the top level (and an IIFE in expression
# position). This test verifies the extracted Go compiles.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-bug3-axiom-panic/

cleanup() {
  rm -rf out *.vo *.vos *.vok *.glob .*.aux
}
trap cleanup EXIT

# Clean previous output
rm -rf out
mkdir -p out

# Run extraction
rocq c -R . Top Test.v

# The axiom marker must be present somewhere in the extracted Go.
if ! grep -q 'panic("AXIOM TO BE REALIZED:' out/*/*.go; then
  >&2 echo "Expected panic(\"AXIOM TO BE REALIZED: ...\") in extracted Go"
  exit 1
fi

# The axiom panic must NOT appear as `return panic(...)` at the
# top level (Go rejects this: panic is a no-value expression).
if grep -E '^[[:space:]]*return[[:space:]]+panic\("AXIOM TO BE REALIZED:' out/*/*.go; then
  >&2 echo "Found 'return panic(\"AXIOM TO BE REALIZED: ...\")' — Bug 3 regression"
  exit 1
fi

# Compile with Go if available — this is the most direct check, since
# `return panic(...)` is precisely what Go rejects.
if command -v go >/dev/null 2>&1; then
  (cd out && go build ./...)
  echo "Go compilation succeeded"
else
  echo "go not found, skipping Go compilation check"
fi

exit 0
