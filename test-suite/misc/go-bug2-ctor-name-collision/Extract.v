(* Drives Separate Extraction so that [Test.v]'s contents land in their
   own Go package ([test]). This is what triggers Bug 2: the inductive
   [ascii] and its constructor [Ascii] both become top-level "Ascii"
   inside the [test] package. *)
From Corelib Require Extraction.
From Top Require Import Test.

Extraction Language Go.
Set Extraction Go Module "bug2test/extracted".
Set Extraction Output Directory "out".

Separate Extraction Test.
