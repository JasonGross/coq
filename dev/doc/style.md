# OCaml Style for Rocq

> Style uniformity is more important than style itself
> -- <cite>Kernigan & Pike, The Practice of Programming</cite>

## Spacing and indentation

- indent your code (using tuareg default)
- no strong constraints in formatting `let in`; possible styles are:
  ```ocaml
  let x = ... in
  ```
  ```ocaml
  let x =
    ... in
  ```
  ```ocaml
  let x =
    ...
  in
  ```
- but: no extra indentation before a `in` coming on next line,
  otherwise, it first shifts further and further on the right,
  reducing the amount of space available; second, it is not robust to
  insertion of a new `let`
- it is established usage to have space around `|` as in
  ```ocaml
   match c with
   | [] | [a] -> ...
   | a::b::l -> ...
  ```
- the tendency is to use the following format which
  limit excessive indentation while providing an interesting "block" aspect
  ```ocaml
  type t =
  | A
  | B of machin

  let f expr = match expr with
  | A -> ...
  | B x -> ...

  let f expr = function
  | A -> ...
  | B x -> ...
  ```
- add spaces around `=` and `==` (make the code "breathe")
  (note that use of ocaml stdlib `=` is discouraged)
- the common usage is to write `let x,y = ... in ...` rather than
  `let (x,y) = ... in ...`
- parenthesizing with either `(` and `)` or with `begin` and `end` is
  common practice
- preferred layout for conditionals:
  ```ocaml
  if condition then
    first-case
  else
    second-case
  ```
- in case of effects in branches, use `begin ... end` rather than
  parentheses
  ```ocaml
  if condition then begin
    instr1;
    instr2
  end else begin
    instr3;
    instr4
  end
  ```
- avoid semicolon after single branch `if`, ie instead of
  ~~~ocaml
  if foo then bar;
  baz
  ~~~
  do
  ~~~ocaml
  let () = if foo then bar in
  baz
  ~~~
- if the first branch raises an exception, avoid the `else`, i.e.
  use
  ```ocaml
  let () = if condition then error "foo" in
  bar
  ```
  instead of
  ```ocaml
  if condition then
    error "foo"
  else
    bar
  ```
- it is the usage not to use `;;` to end OCaml sentences (however,
  inserting `;;` can be useful for debugging syntax errors crossing
  the boundary of functions)
- relevant options in tuareg:
  ```
  (setq tuareg-in-indent 2)
  (setq tuareg-with-indent 0)
  (setq tuareg-function-indent 0)
  (setq tuareg-let-always-indent nil)
  ```
- when a match fails to compile due to unbound constructors (eg
  `match x with VarRef x -> bla | ConstRef x -> bli | _ -> blo` when
  `GlobRef` is not open) it can be resolved in several ways:
  + locally or globally open `GlobRef`
  + type annotate `x : GlobRef.t` (where it is introduced, or in the `match` expression, whichever is nicer)
  + annotate the first branch `GlobRef.VarRef x -> bla`
    this last solution is not robust to branch reordering so should not be prefered

## Coding methodology

- no catchall `try ... with _ -> ...` which catches even `Sys.Break` (Ctrl-C),
  `Out_of_memory`, `Stack_overflow`, etc.
  at least, use `try with e when CErrors.noncritical e -> ...`
- do not abuse fancy combinators: sometimes what a `let rec` loop
  does is more readable and simpler to grasp than what a `fold` does
- do not break abstractions: if an internal property is hidden
  behind an interface, do no rely on it in code which uses this
  interface (e.g. do not use `List.map` thinking it is left-to-right,
  use `map_left`)
- in particular, do not use `=` on abstract types: there is no
  reason a priori that it is the intended equality on this type; use the
  `equal` function normally provided with the abstract type
- avoid polymorphically typed `=` whose implementation is not
  optimized in OCaml and which has moreover no reason to be the
  intended implementation of the equality when it comes to be
  instantiated on a particular type (e.g. use `List.mem_f`,
  `List.assoc_f`, rather than `List.mem`, `List.assoc`, etc, unless it is
  absolutely clear that `=` will implement the intended equality, and
  with the right complexity)
- any new general-purpose enough combinator on list should be put in
  `cList.ml`, on type option in `option.ml`, etc.
- unless for a good reason not to do so, follow the style of the
  surrounding code in the same file as much as possible,
  the general guidelines are otherwise "let spacing breathe" (we
  have large screen nowadays), "make your code easy to read and
  to understand"
- document what is tricky, but do not overdocument, sometimes the
  choice of names and the structure of the code are better
  documentation than a long discourse; use of unicode in comments is
  welcome if it can make comments more readable (then
  `toggle-enable-multibyte-characters` can help when using the
  debugger in emacs)
- all of initial `open Module`, or of small-scope `let open Module in` or `Module.(...)`, or
  per-ident `Module.foo` are common practices.
  `open Module` in the middle of a file should probably be avoided (keep global opens at the top)

## Choice of variable names

- be consistent when naming from one function to another
- be consistent with the naming adopted in the functions from the
  same file, or with the naming used elsewhere by similar functions
- use variable names which express meaning
- keep `cst` or `con` for constants and avoid it for constructors which is
  otherwise a source of confusion
- for constructors, use `ctor` in type constructor (resp. `ctoru` in
  constructor puniverse); avoid `constr` for `constructor` which
  could be think as the name of an arbitrary Constr.t
- for inductive types, use `ind` in the type inductive (resp `indu`
  in inductive puniverse)
- for `env`, use `env`
- for `evar_map`, use `sigma`, with tolerance for `evm` and `evd`
- for `named_context` or `rel_context`, use `ctxt` or `ctx` (or `sign`)
- for formal/actual indices of inductive types: `realdecls`, `realargs`
- for formal/actual parameters of inductive types: `paramdecls`, `paramargs`
- for terms, use e.g. `c`, `b`, `a`, ...
- if a term is known to be a function: `f`, ...
- if a term is known to be a type: `t`, `u`, `typ`, ...
- for a declaration, use `d` or `decl`
- for errors, exceptions, use `e`

## Common OCaml pitfalls

- in
  ```ocaml
  match ... with Case1 -> try ... with ... -> ... | Case2 -> ...
  ```
  or in
  ```ocaml
  match ... with Case1 -> match ... with SubCase -> ... | Case2 -> ...
  ```
  parentheses (or `begin`/`end` which looks nicer) are needed around the `try` and the inner `match`
- in
  ```ocaml
  if ... then ... else ... ++ ...
  ```
  the default parenthesizing
  is somehow counter-intuitive; use
  ```ocaml
  (if ... then ... else ...) ++ ...
  ```
- in `let myspecialfun = mygenericfun args`, be sure that it does not
  do side-effect; prefer otherwise
  ```ocaml
  let myspecialfun arg = mygenericfun args arg
  ```
  to ensure that the function is evaluated at
  runtime.
