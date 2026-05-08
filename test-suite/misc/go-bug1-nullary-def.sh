#!/usr/bin/env bash

# Regression test for Bug 1 in Go extraction: a nullary Definition is
# emitted as `func Name() any { ... }`, but use sites referencing it
# previously produced the bare `Name` (a function value of type
# `func() any`) where an `any` value was expected. The fix emits
# `Name()` at the use site.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-bug1-nullary-def/

cleanup() {
  rm -rf out *.vo *.vos *.vok *.glob .*.aux
}
trap cleanup EXIT

# Clean previous output
rm -rf out
mkdir -p out

# Run extraction
rocq c -R . Top Test.v

# Verify expected files were generated
for f in out/go.mod out/test/test.go; do
  if [ ! -f "$f" ]; then
    >&2 echo "Missing expected file: $f"
    exit 1
  fi
done

# Verify go.mod content
if ! grep -q 'module bug1test/extracted' out/go.mod; then
  >&2 echo "go.mod does not contain expected module path"
  exit 1
fi

# The nullary definition should be emitted as a zero-arg function.
if ! grep -q '^func Ehdr_size() any {' out/test/test.go; then
  >&2 echo "test.go: nullary definition Ehdr_size not emitted as func() any"
  exit 1
fi

# Bug 1 regression check: the use site must call Ehdr_size, i.e. emit
# `Ehdr_size()`, not the bare function value `Ehdr_size`.
# In Use_ehdr the reference is the second argument to nat.Add.
if ! grep -q 'nat.Add(n, Ehdr_size())' out/test/test.go; then
  >&2 echo "test.go: Use_ehdr does not call Ehdr_size() (Bug 1 regression)"
  exit 1
fi

# In Double_ehdr the reference is the argument passed to Use_ehdr.
if ! grep -q 'Use_ehdr(Ehdr_size())' out/test/test.go; then
  >&2 echo "test.go: Double_ehdr does not call Ehdr_size() (Bug 1 regression)"
  exit 1
fi

# Belt-and-suspenders: explicitly reject the buggy bare-name forms that
# the pre-fix extractor produced.
if grep -qE 'nat\.Add\(n, Ehdr_size\)' out/test/test.go; then
  >&2 echo "test.go: bare Ehdr_size passed to nat.Add (Bug 1 regression)"
  exit 1
fi

if grep -qE 'Use_ehdr\(Ehdr_size\)' out/test/test.go; then
  >&2 echo "test.go: bare Ehdr_size passed to Use_ehdr (Bug 1 regression)"
  exit 1
fi

# Compile with Go if available
if command -v go >/dev/null 2>&1; then
  (cd out && go build ./...)
  echo "Go compilation succeeded"
else
  echo "go not found, skipping Go compilation check"
fi

exit 0
