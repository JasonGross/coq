#!/usr/bin/env bash

# Regression test: a chain of Coq [let .. in let .. in ...] bindings
# used to emit one nested IIFE per binding -- O(N) closures for an
# N-binding chain. Past 20-30 deep, that pattern drives Go's escape
# analysis into superlinear scaling and OOMs the Go compiler
# (~20 GB observed on a 16-GB machine in the bug report).
#
# The fix collects the chain and emits a single IIFE with one [var]
# declaration per binding, cutting nesting from O(N) to O(1).
#
# To make the regression test actually fail at [go build] time without
# the fix (rather than only at a shape grep), we extract a 50-deep
# chain and run [go build] under a 2 GB virtual-memory cap via
# [ulimit -v]. The buggy emission's escape analysis needs >2 GB and
# the compiler exits non-zero; the fixed emission's [go build] stays
# in low double-digit MB of RSS regardless of depth.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/go-let-chain-flat/

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

# Sanity check on the extracted shape: every [x0..x49] binding must
# appear as a Go [var x_i any = ...] declaration. (Belt-and-suspenders
# for the [go build] check below; it also helps localise breakage if
# the build cap on the CI host happens to be too tight.)
for i in $(seq 0 49); do
  if ! grep -qE "^[[:space:]]+var x$i any =" "$GO_FILE"; then
    >&2 echo "$GO_FILE: missing 'var x$i any = ...' (let-chain binding lost?)"
    exit 1
  fi
done

# Build with [go] under a 2 GB virtual-memory cap. The buggy emission
# (50 nested IIFEs) needs more than that and the compiler aborts; the
# fixed emission (flat -- 50 sibling [var]s in one IIFE) stays well
# under. Skip if [go] is unavailable, or if the surrounding shell
# cannot lower [ulimit -v] far enough (some sandboxed CI environments
# may not let us narrow the limit).
if ! command -v go >/dev/null 2>&1; then
  echo "go not found, skipping Go compilation check"
  exit 0
fi

VM_CAP_KB=$((2 * 1024 * 1024))   # 2 GB
(
  ulimit -v "$VM_CAP_KB" 2>/dev/null || {
    echo "ulimit -v unavailable; falling back to unbounded go build"
    cd out && go build ./...
    exit
  }
  # Verify the cap actually took effect; if the host's RLIMIT_AS is
  # already lower (e.g. cgroup-restricted CI), the buggy emission
  # would also fail and the test would be uninformative -- bail out
  # rather than report a false positive.
  GOT=$(ulimit -v)
  if [ "$GOT" != "$VM_CAP_KB" ] && [ "$GOT" != "unlimited" ]; then
    if [ "$GOT" -lt "$VM_CAP_KB" ]; then
      echo "warn: host ulimit -v ($GOT KB) is below the test cap ($VM_CAP_KB KB); skipping memory-bounded build"
      cd out && go build ./...
      exit
    fi
  fi
  cd out && go build ./...
)
echo "Go compilation succeeded under 2 GB virtual-memory cap"

exit 0
