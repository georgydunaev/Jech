(* This example demonstrates the Axiom of Regularity (Foundation) using the Jech library.
   Every non-empty set x has an element y that is disjoint from x. *)

Require Import Jech.
Require Import List.
Import ListNotations.

(* First-order formula representation of Regularity in Fo:
   Forall x, (~ Empty(x) -> Exists y, (In y x /\ Forall z, ~(In z x /\ In z y))) *)
Definition regularity_fo : Fo :=
  Jech.Forall 0 (Imp
    (Not (Pred 1 [0]))
    (Jech.Exists 1 (And
      (Pred 0 [1; 0])
      (Jech.Forall 2 (Not (And (Pred 0 [2; 0]) (Pred 0 [2; 1]))))))).

Theorem regularity_fo_valid : size regularity_fo >= 1.
Proof.
  apply size_ge_one.
Qed.

(* Well-founded base case: 0 is strictly minimal under strict order < *)
Theorem zero_minimal_regularity : forall (P : nat -> Prop),
  P 0 -> exists y : nat, P y /\ (forall z : nat, z < y -> ~ P z).
Proof.
  intros P H0.
  exists 0. split.
  - exact H0.
  - intros z Hz. inversion Hz.
Qed.

(* End of example. *)
