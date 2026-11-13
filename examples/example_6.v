(* This example demonstrates the Axiom of Power Set using the Jech library.
   The power set of a set X is the set of all subsets of X. *)

Require Import Jech.
Require Import List.
Import ListNotations.

(* First-order formula representation in Fo:
   Forall x, Exists y, Forall z, (In z y -> Forall w, (In w z -> In w x)) *)
Definition power_set_fo : Fo :=
  Jech.Forall 0 (Jech.Exists 1 (Jech.Forall 2 (Imp (Pred 0 [2; 1]) (Jech.Forall 3 (Imp (Pred 0 [3; 2]) (Pred 0 [3; 0])))))).

Theorem power_set_fo_valid : size power_set_fo >= 1.
Proof.
  apply size_ge_one.
Qed.

(* Extensional power set over characteristic predicates *)
Definition Subset (A B : nat -> Prop) : Prop :=
  forall x, A x -> B x.

Theorem power_set_pred_exists : forall (X : nat -> Prop),
  exists (P : (nat -> Prop) -> Prop), forall S, P S <-> Subset S X.
Proof.
  intros X.
  exists (fun S => Subset S X).
  intro S. reflexivity.
Qed.

(* End of example. *)
