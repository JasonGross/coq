#!/usr/bin/env bash

# Test modular Go extraction: Separate Extraction produces multiple
# Go packages with cross-package imports that compile with go build.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-modular-extraction/

# Clean previous output
rm -rf out
mkdir -p out

# Compile Rocq source files
rocq c -R . Top Base.v
rocq c -R . Top Consumer.v

# Run extraction
rocq c -R . Top Extract.v

# Verify expected files were generated
for f in out/go.mod out/base/base.go out/consumer/consumer.go; do
  if [ ! -f "$f" ]; then
    >&2 echo "Missing expected file: $f"
    exit 1
  fi
done

# Verify go.mod content
if ! grep -q 'module gotest/extracted' out/go.mod; then
  >&2 echo "go.mod does not contain expected module path"
  exit 1
fi

# Verify cross-package import in consumer
if ! grep -q '"gotest/extracted/base"' out/consumer/consumer.go; then
  >&2 echo "consumer.go does not import base package"
  exit 1
fi

# Verify identifiers are capitalized (Go export visibility)
if ! grep -q 'func Myadd' out/base/base.go; then
  >&2 echo "base.go: Myadd not capitalized"
  exit 1
fi

if ! grep -q 'func Mydouble' out/consumer/consumer.go; then
  >&2 echo "consumer.go: Mydouble not capitalized"
  exit 1
fi

# Verify mutual recursion uses init() pattern
if ! grep -q 'func init()' out/base/base.go; then
  >&2 echo "base.go: missing init() for mutual recursion"
  exit 1
fi

# Compile with Go if available
if command -v go >/dev/null 2>&1; then
  (cd out && go build ./...)
  echo "Go compilation succeeded"
else
  echo "go not found, skipping Go compilation check"
fi

# Clean up
rm -rf out *.vo *.vos *.vok *.glob .*.aux

exit 0
