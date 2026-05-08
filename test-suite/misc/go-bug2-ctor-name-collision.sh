#!/usr/bin/env bash

# Regression test for Bug 2: Go extraction must not emit a duplicate
# top-level declaration when an inductive's Go name collides with its
# constructor's Go name (e.g. [Inductive ascii := Ascii ...] would
# previously emit two [type Ascii ...] declarations and Go would reject
# the file with "Ascii redeclared in this block").

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-bug2-ctor-name-collision/

cleanup() {
  rm -rf out *.vo *.vos *.vok *.glob .*.aux
}
trap cleanup EXIT

# Clean previous output
rm -rf out
mkdir -p out

# Compile the source module (defines [ascii] / [Ascii] / [foo] / [MkFoo]).
rocq c -R . Top Test.v

# Run extraction. [Extract.v] does the [Separate Extraction Test], which
# places the contents of [Test.v] into their own Go package [test] —
# this is precisely the configuration that produced the duplicate
# top-level [type Ascii] before the fix.
rocq c -R . Top Extract.v

GO_FILE=out/test/test.go

if [ ! -f "$GO_FILE" ]; then
  >&2 echo "Missing expected file: $GO_FILE"
  exit 1
fi

# The inductive type [ascii] should still be declared as [type Ascii interface{...}].
if ! grep -q 'type Ascii interface{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing 'type Ascii interface{' (inductive type declaration)"
  exit 1
fi

# The constructor [Ascii] should be renamed to [MkAscii] to avoid the collision.
if ! grep -q 'type MkAscii struct{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing 'type MkAscii struct{' (renamed constructor)"
  exit 1
fi

# The bug would manifest as a second [type Ascii struct{...}] declaration.
if grep -q 'type Ascii struct{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: found 'type Ascii struct{' — collision with the inductive type is back"
  exit 1
fi

# The constructor application should also use the renamed identifier.
if ! grep -q 'MkAscii{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing 'MkAscii{' (constructor application using renamed name)"
  exit 1
fi

# Control: [MkFoo] does not collide with [Foo], so its name must be left alone
# (i.e. NOT renamed to [MkMkFoo]).
if ! grep -q 'type MkFoo struct{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: missing 'type MkFoo struct{' (non-colliding constructor)"
  exit 1
fi

if grep -q 'type MkMkFoo struct{' "$GO_FILE"; then
  >&2 echo "$GO_FILE: found 'type MkMkFoo struct{' — rename fired without a collision"
  exit 1
fi

# Compile with Go if available. This is the most direct check of the bug:
# without the fix, Go would reject the file because of the duplicate
# [type Ascii ...] declarations.
if command -v go >/dev/null 2>&1; then
  (cd out && go build ./...)
  echo "Go compilation succeeded"
else
  echo "go not found, skipping Go compilation check"
fi

exit 0
