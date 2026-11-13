(* This is a simple example demonstrating the use of the Jech library. *)

Require Import Jech.
Require Import List.
Import ListNotations.

(* Define a simple set representation and demonstrate membership queries. *)
Definition my_set : list nat := [1; 2; 3].

Compute In 1 my_set.
Compute In 4 my_set.

(* End of example. *)
