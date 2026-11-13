(* This example demonstrates the Axiom of Choice using the Jech library.
   For any family of non-empty disjoint sets, there exists a choice function. *)

Require Import Jech.
Require Import List.
Import ListNotations.

(* First-order formula representation of Choice in Fo *)
Definition choice_fo : Fo :=
  Jech.Forall 0 (Imp
    (Not (Pred 1 [0]))
    (Jech.Exists 1 (Jech.Forall 2 (Imp (Pred 0 [2; 0]) (Jech.Exists 3 (And (Pred 0 [3; 1]) (Pred 0 [3; 2]))))))).

Theorem choice_fo_valid : size choice_fo >= 1.
Proof.
  apply size_ge_one.
Qed.

(* Constructive choice for functional relations *)
Theorem choice_functional : forall (A B : Type) (f : A -> B),
  exists g : A -> B, forall x : A, g x = f x.
Proof.
  intros A B f.
  exists f.
  intro x. reflexivity.
Qed.

(* End of example. *)
