(* Testing some backtracking traces *)

Ltac t1 := idtac + idtac.
Ltac t2 := fail.

Goal True.
  Info 0 t1. Undo.
  Info 1 t1. Undo.
  Info 2 t1. Undo.
  Info 3 t1. Undo.
  Trace 0 t1. Undo.
  Trace 1 t1. Undo.
  Trace 2 t1. Undo.
  Trace 3 t1. Undo.
  Info 0 try (t1; t2). Undo.
  Info 1 try (t1; t2). Undo.
  Info 2 try (t1; t2). Undo.
  Info 3 try (t1; t2). Undo.
  Trace 0 try (t1; t2). Undo.
  Trace 1 try (t1; t2). Undo.
  Trace 2 try (t1; t2). Undo.
  Trace 3 try (t1; t2). Undo.
  constructor.
Qed.
