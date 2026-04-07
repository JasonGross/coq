(* Base module: defines types and functions *)
Inductive mynat := MyO | MyS (n : mynat).

Fixpoint myadd (n m : mynat) : mynat :=
  match n with MyO => m | MyS p => MyS (myadd p m) end.

Fixpoint myeven (n : mynat) : bool :=
  match n with MyO => true | MyS p => myodd p end
with myodd (n : mynat) : bool :=
  match n with MyO => false | MyS p => myeven p end.
