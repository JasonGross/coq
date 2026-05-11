#!/usr/bin/env bash

# Regression test for Go extraction of a single-constructor CoInductive:
# the previous emission declared a thunk-wrapping [type T struct{ Force
# func() T_body }] plus a separate [T_body] struct, but constructor sites
# referred to the constructor's name (e.g. [Coq_go]) which was never
# declared. Go rejected the file with "undefined: Coq_go".
#
# The fix emits the same shape used for ordinary records: one interface
# named after the type, one struct named after the constructor, plus
# the marker method. This regression test verifies the extracted Go
# compiles, which is the most direct end-to-end check.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-coinductive-ctor/

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

# The CoInductive type [itree] should be emitted as a Go interface,
# matching the variant/record pattern.
if ! grep -q 'type Itree interface{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing 'type Itree interface{' (interface for the type)"
  exit 1
fi

# The constructor [go] (sanitised to [Coq_go] because [go] is a Go keyword)
# should be the name of the struct.
if ! grep -q 'type Coq_go struct' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing 'type Coq_go struct' (constructor-named struct)"
  exit 1
fi

# The marker method binds the struct to the interface.
if ! grep -q 'func (Coq_go) IsItree()' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing marker method 'func (Coq_go) IsItree()'"
  exit 1
fi

# Belt-and-suspenders: the buggy [Itree_body] declaration must not return.
if grep -q 'type Itree_body' "$GO_FILE"; then
  >&2 echo "$GO_FILE: found stale 'type Itree_body' declaration (Bug 2 regression)"
  exit 1
fi

# And the buggy thunk-wrapping Itree declaration must not return either.
if grep -q 'type Itree struct{ Force' "$GO_FILE"; then
  >&2 echo "$GO_FILE: found stale thunk-wrapping 'type Itree struct{ Force ...'"
  exit 1
fi

# Compile with Go if available. This is the most direct check: without
# the fix, Go rejects with "undefined: Coq_go".
if command -v go >/dev/null 2>&1; then
  (cd out && go build ./...)
  echo "Go compilation succeeded"
else
  echo "go not found, skipping Go compilation check"
fi

exit 0
