(* Regression test: a Coq [match] arm whose RHS extracts to a Go IIFE
   ([func() any { switch ... }()]) used to break across two lines when
   the surrounding context was past Format's [max_indent] threshold
   (margin - 10 = 68 by default). Opening the IIFE's [v 0] box at a
   column past [max_indent] triggers Format's "tabulate from the left
   margin" behaviour: the preceding [return ] sits alone at the end of
   one line and the [func() any {] starts a fresh line. Go's automatic
   semicolon insertion then reads the [return] as [return;] (returns
   nothing) followed by a dead [func() any { ... }()] expression-
   statement, and the file fails to compile with "not enough return
   values" (or, when the enclosing function returns [any], silently
   returns the zero value).

   8-deep nested matches on [bool] are enough to push the inner v-box
   past the default max_indent and reproduce the bug. *)
From Corelib Require Extraction.

Definition encode (a b c d e f g h : bool) : nat :=
  match a with
  | true =>
    match b with
    | true =>
      match c with
      | true =>
        match d with
        | true =>
          match e with
          | true =>
            match f with
            | true =>
              match g with
              | true => if h then 1 else 2
              | false => 3
              end
            | false => 4
            end
          | false => 5
          end
        | false => 6
        end
      | false => 7
      end
    | false => 8
    end
  | false => 9
  end.

Extraction Language Go.
Set Extraction Go Module "asitest/extracted".
Set Extraction Output Directory "out".

Separate Extraction encode.
