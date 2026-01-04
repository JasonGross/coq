(* Test for Printing Fully Qualified option *)

Module A.
  Definition foo := 1.
End A.

Module B.
  Definition foo := 2.
End B.

(* Default: use shortest name *)
Check A.foo.
Check B.foo.

(* With fully qualified printing *)
Set Printing Fully Qualified.
Check A.foo.
Check B.foo.

(* Back to default *)
Unset Printing Fully Qualified.
Check A.foo.
Check B.foo.

(* Test with deeper nesting *)
Module C.
  Module D.
    Definition bar := 3.
  End D.
End C.

Set Printing Fully Qualified.
Check C.D.bar.
Unset Printing Fully Qualified.
Check C.D.bar.

(* Test Search with Printing Fully Qualified *)
Set Search Output Name Only.
Search "True".
Set Printing Fully Qualified.
Search "True".
Unset Printing Fully Qualified.
Unset Search Output Name Only.
