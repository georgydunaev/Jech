(* This is an advanced example demonstrating the use of the Jech library with ZFC axioms and theorems. *)

(* Import the Jech library. *)
Require Import Jech.

(* Define a set and demonstrate the use of ZFC axioms. *)
Definition my_set := {1, 2, 3}.

(* Axiom of Extensionality: Two sets are equal if they have the same elements. *)
Definition another_set := {1, 2, 3}.
Compute my_set = another_set.

(* Axiom of Pairing: For any two sets, there exists a set that contains both of them. *)
Definition pair_set := {my_set, another_set}.
Print pair_set.

(* Axiom of Union: For any collection of sets, there exists a set that contains all the elements of the sets in the collection. *)
Definition union_set := union my_set another_set.
Print union_set.

(* Theorem 1.1: The intersection of any two sets is a set. *)
Definition intersection_set := my_set ∩ another_set.
Print intersection_set.

(* Theorem 1.2: The difference of any two sets is a set. *)
Definition difference_set := my_set - another_set.
Print difference_set.

(* End of example. *)