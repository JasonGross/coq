(* Regression test for Bug 1: nullary Definitions referenced from other
   functions used to be emitted as the bare function name (passing the
   function pointer) instead of a call to the function. *)
From Corelib Require Extraction.

(* Nullary Definition with first-order type: extracted as
   `func Ehdr_size() any { ... }`. *)
Definition ehdr_size : nat := 5.

(* Function that references the nullary definition. The buggy extractor
   emitted `Ehdr_size` (bare) at the use site; the fix emits `Ehdr_size()`. *)
Definition use_ehdr (n : nat) : nat := n + ehdr_size.

(* A second consumer to make the call site appear in a typical position. *)
Definition double_ehdr : nat := use_ehdr ehdr_size.

Extraction Language Go.
Set Extraction Go Module "bug1test/extracted".
Set Extraction Output Directory "out".

Separate Extraction ehdr_size use_ehdr double_ehdr.
