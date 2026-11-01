- **Added:**
  Warning ``generated-hyp-name`` (category ``fragile``, disabled by
  default). When a tactic sentence lets Rocq choose some hypothesis
  names (for example ``intros``, ``destruct n`` or ``induction n``
  without an ``as`` clause) and a later sentence of the same proof
  uses one of them, the warning reports the generated names at the
  introducing sentence. For the simple sentence shapes it also gives
  a replacement that names them, as text and as a quickfix
  (`#PRNUM <https://github.com/rocq-prover/rocq/pull/PRNUM>`_,
  by Jason Gross).
