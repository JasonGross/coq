(* Testing some basic traces *)

Ltac t1 := intuition.
Ltac t2 := idtac.
Ltac t3 := fail.

Goal True.
  Info 0 t1. Undo.
  Info 1 t1. Undo.
  Info 2 t1. Undo.
  Info 3 t1. Undo.
  Trace 0 t1. Undo.
  Trace 1 t1. Undo.
  Trace 2 t1. Undo.
  Trace 3 t1. Undo.
  Info 0 t2. Undo.
  Info 1 t2. Undo.
  Info 2 t2. Undo.
  Info 3 t2. Undo.
  Trace 0 t2. Undo.
  Trace 1 t2. Undo.
  Trace 2 t2. Undo.
  Trace 3 t2. Undo.
  Info 0 try (t2; t3). Undo.
  Info 1 try (t2; t3). Undo.
  Info 2 try (t2; t3). Undo.
  Info 3 try (t2; t3). Undo.
  Trace 0 try (t2; t3). Undo.
  Trace 1 try (t2; t3). Undo.
  Trace 2 try (t2; t3). Undo.
  Trace 3 try (t2; t3). Undo.
  constructor.
Qed.
