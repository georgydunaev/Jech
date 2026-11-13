(* Example demonstrating set operations via list representations *)

Require Import Jech.
Require Import List.
Require Import PeanoNat.
Import ListNotations.

Definition set_a : list nat := [1; 2; 3; 4; 5].
Definition set_b : list nat := [4; 5; 6; 7; 8].

(* List-based union *)
Definition list_union (l1 l2 : list nat) : list nat :=
  l1 ++ filter (fun x => if existsb (Nat.eqb x) l1 then false else true) l2.

(* List-based intersection *)
Definition list_intersection (l1 l2 : list nat) : list nat :=
  filter (fun x => existsb (Nat.eqb x) l2) l1.

(* List-based difference *)
Definition list_difference (l1 l2 : list nat) : list nat :=
  filter (fun x => if existsb (Nat.eqb x) l2 then false else true) l1.

Compute list_union set_a set_b.
Compute list_intersection set_a set_b.
Compute list_difference set_a set_b.

(* End of example. *)
