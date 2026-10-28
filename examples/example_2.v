(* This is a simple example demonstrating the use of the Jech library without requiring compilation. *)

(* Import the Jech library. *)
Require Import Jech.

(* Define a simple set and demonstrate basic operations. *)
Definition my_set := {1, 2, 3}.

(* Check if an element is in the set. *)
Compute in 1 my_set.
Compute in 4 my_set.

(* End of example. *)