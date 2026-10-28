(* This is an advanced example demonstrating more complex set operations using the Jech library. *)

(* Import the Jech library. *)
Require Import Jech.

(* Define two sets for demonstration purposes. *)
Definition set_a := {1, 2, 3, 4, 5}.
Definition set_b := {4, 5, 6, 7, 8}.

(* Demonstrate set union. *)
Compute union set_a set_b.

(* Demonstrate set intersection. *)
Compute intersection set_a set_b.

(* Demonstrate set difference. *)
Compute difference set_a set_b.

(* Define a more complex set using a predicate. *)
Definition even_numbers := {x | x in {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} & even x}.

(* Check if an element is in the complex set. *)
Compute in 2 even_numbers.
Compute in 3 even_numbers.

(* End of example. *)