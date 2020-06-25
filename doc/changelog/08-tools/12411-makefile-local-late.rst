- **Added:**
  ``coq_makefile``\-made ``Makefile``\s now include the ``.local``
  file at the very end, in case the user wants to have access to more
  variables.  Note that this may break some very rare use-cases where
  the ``.local`` file was used to override some variables in the
  ``Makefile``; if you are making use of this, please open an issue on
  the bug tracker and we can add back support for overriding variables
  with inclusion of an local file earlier on (`#12411
  <https://github.com/coq/coq/pull/12411>`_, fixes `#10912
  <https://github.com/coq/coq/issues/10912>`_, by Jason Gross).
