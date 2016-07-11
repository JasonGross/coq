Definition even :=
 fix
    even (n:nat) : bool := match n with O => true  | (S p) => (odd p)  end
  with
    odd  (n:nat) : bool := match n with O => false | (S p) => (even p) end
  for even.
