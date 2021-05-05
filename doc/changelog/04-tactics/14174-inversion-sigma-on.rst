- **Added:**
  :tacn:`inversion_sigma` can now be applied to a specified hypothesis
  and additionally supports intropatterns, so it can be used much like
  :tacn:`induction` and :tacn:`inversion`.  This required a minor
  tweak in the goals that it generates, which are now in terms of
  ``eq_sigT_uncurried`` rather than ``eq_sigT`` (`#14174
  <https://github.com/coq/coq/pull/14174>`_, by Jason Gross).
