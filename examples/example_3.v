(* This is an example demonstrating basic set-theoretic operations using predicates. *)

Require Import Jech.

Definition SetPred := nat -> Prop.
Definition Elem (x : nat) (A : SetPred) : Prop := A x.

(* Theorem 1.1: Intersection of set predicates *)
Theorem intersection : forall A B : SetPred, exists C : SetPred, forall x : nat, Elem x C <-> Elem x A /\ Elem x B.
Proof.
  intros A B.
  exists (fun x => Elem x A /\ Elem x B).
  intro x. reflexivity.
Qed.

(* Theorem 1.2: Difference of set predicates *)
Theorem difference : forall A B : SetPred, exists C : SetPred, forall x : nat, Elem x C <-> Elem x A /\ ~ Elem x B.
Proof.
  intros A B.
  exists (fun x => Elem x A /\ ~ Elem x B).
  intro x. reflexivity.
Qed.

(* End of example. *)
