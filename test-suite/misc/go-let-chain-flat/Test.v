(* Regression test: a chain of Coq [let x := e in let y := e' in ...]
   bindings used to extract to one nested IIFE per binding, producing
   N levels of [(func(x any) any { return ... })(e)] closures for a
   chain of length N. Past 20-30 levels this drives Go's escape
   analysis into superlinear scaling and OOMs the Go compiler --
   ~20 GB observed on a 16-GB machine in the bug report.

   The fix collects the chain and emits a single IIFE with multiple
   [var] declarations followed by [return body], cutting nesting from
   O(N) to O(1).

   50 lets is enough to make the buggy [go build] need >2GB of
   virtual address space (which the [ulimit -v] cap in the driver
   denies); the fixed extraction stays well under regardless of
   depth. *)
From Corelib Require Extraction.

Definition deep (n : nat) : nat :=
  let x0  := n   + 1 in
  let x1  := x0  + 1 in
  let x2  := x1  + 1 in
  let x3  := x2  + 1 in
  let x4  := x3  + 1 in
  let x5  := x4  + 1 in
  let x6  := x5  + 1 in
  let x7  := x6  + 1 in
  let x8  := x7  + 1 in
  let x9  := x8  + 1 in
  let x10 := x9  + 1 in
  let x11 := x10 + 1 in
  let x12 := x11 + 1 in
  let x13 := x12 + 1 in
  let x14 := x13 + 1 in
  let x15 := x14 + 1 in
  let x16 := x15 + 1 in
  let x17 := x16 + 1 in
  let x18 := x17 + 1 in
  let x19 := x18 + 1 in
  let x20 := x19 + 1 in
  let x21 := x20 + 1 in
  let x22 := x21 + 1 in
  let x23 := x22 + 1 in
  let x24 := x23 + 1 in
  let x25 := x24 + 1 in
  let x26 := x25 + 1 in
  let x27 := x26 + 1 in
  let x28 := x27 + 1 in
  let x29 := x28 + 1 in
  let x30 := x29 + 1 in
  let x31 := x30 + 1 in
  let x32 := x31 + 1 in
  let x33 := x32 + 1 in
  let x34 := x33 + 1 in
  let x35 := x34 + 1 in
  let x36 := x35 + 1 in
  let x37 := x36 + 1 in
  let x38 := x37 + 1 in
  let x39 := x38 + 1 in
  let x40 := x39 + 1 in
  let x41 := x40 + 1 in
  let x42 := x41 + 1 in
  let x43 := x42 + 1 in
  let x44 := x43 + 1 in
  let x45 := x44 + 1 in
  let x46 := x45 + 1 in
  let x47 := x46 + 1 in
  let x48 := x47 + 1 in
  let x49 := x48 + 1 in
  x49 + x49.

Extraction Language Go.
Set Extraction Go Module "letchain/extracted".
Set Extraction Output Directory "out".

Separate Extraction deep.
