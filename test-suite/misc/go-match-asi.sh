#!/usr/bin/env bash

# Regression test: deeply nested Coq [match] arms used to extract to
# Go where [return func() any { ... }()] could break across two lines
# at sufficient indent (the [v 0] box for the IIFE opens past
# Format's max_indent and gets tabulated to the left margin). The
# break is fatal -- Go's ASI inserts a semicolon after the bare
# [return], turning the IIFE into a dead expression-statement and
# making the file fail to compile with "not enough return values".

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-match-asi/

cleanup() {
  rm -rf out *.vo *.vos *.vok *.glob .*.aux
}
trap cleanup EXIT

# Clean previous output
rm -rf out
mkdir -p out

# Run extraction
rocq c -R . Top Test.v

GO_FILE=out/test/test.go

if [ ! -f "$GO_FILE" ]; then
  >&2 echo "Missing expected file: $GO_FILE"
  exit 1
fi

# Direct regression check: no line consisting only of whitespace and
# 'return' (with optional trailing whitespace). Pre-fix, the bug
# produced exactly this -- a bare 'return' alone on a line.
if grep -nE '^[[:space:]]+return[[:space:]]*$' "$GO_FILE"; then
  >&2 echo "$GO_FILE: bare 'return' at end of line (Bug 1 regression: ASI splits return from its expression)"
  exit 1
fi

# Belt-and-suspenders: every 'return' must be followed on the same
# line by a non-empty expression. The pre-fix output had several
# 'return\n<indent>func()' pairs which this rejects.
if grep -nE '\breturn$' "$GO_FILE"; then
  >&2 echo "$GO_FILE: 'return' immediately followed by newline (Bug 1 regression)"
  exit 1
fi

# Compile with Go if available. This is the most direct check: without
# the fix, Go rejects with "not enough return values".
if command -v go >/dev/null 2>&1; then
  (cd out && go build ./...)
  echo "Go compilation succeeded"
else
  echo "go not found, skipping Go compilation check"
fi

exit 0
