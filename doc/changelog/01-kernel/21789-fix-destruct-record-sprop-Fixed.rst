- **Fixed:**
  Primitive records in constant sorts (Set, Prop, Type) with only SProp
  fields now have eta conversion, fixing ``destruct`` on such records
  (`#21789 <https://github.com/rocq-prover/rocq/pull/21789>`_,
  fixes `#21788 <https://github.com/rocq-prover/rocq/issues/21788>`_,
  by Jason Gross).
