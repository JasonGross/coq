(* Extraction command: produces modular Go output *)
From Corelib Require Extraction.
From Top Require Import Base Consumer.

Extraction Language Go.
Set Extraction Go Module "gotest/extracted".
Set Extraction Output Directory "out".

Separate Extraction mydouble test_even mylength myeven myodd myadd.
