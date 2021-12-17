Require Import String.
Require Import SimpleIO.SimpleIO.

Import IO.Notations.

Local Open Scope io_scope.
Open Scope string_scope.

Definition main : IO unit :=
  print_endline "Hello world!";;
  print_endline "Extracted from coq!!".

RunIO main.
