(* Theorems derived from the axioms of ZFC *)
(* This file contains theorems that are mechanically proved from the ZFC axioms
   stated in `axioms.v`. Theorems that rely on a specific axiom are noted below. *)

(* ================================================================= *)
(* Imports *)
(* ================================================================= *)
Require Import ZArith ZFC axioms.

(* ================================================================= *)
(* Theorem: The empty set is unique *)
(* ================================================================= *)
(* Statement: forall x, x = empty_set <-> forall y, y \notin x *)
(* Proof uses: extensionality axiom *)
Theorem empty_set_unique : forall x, x = empty_set <-> forall y, y \notin x.
Proof.
  intros x.
  split.
  - intros H. destruct H. reflexivity.
  - intros H. intros y. apply H. apply extensionality. intros z. split; intro H1; contradiction.
Qed.

(* ================================================================= *)
(* Theorem: The union of two sets is a set *)
(* ================================================================= *)
(* Statement: forall x y, exists z, forall w, w \in z <-> w \in x \/ w \in y *)
(* Proof uses: pairing axiom *)
Theorem union_set : forall x y, exists z, forall w, w \in z <-> w \in x \/ w \in y.
Proof.
  intros x y. apply pairing. intros w. split.
  - intro H. destruct H as [H1 | H2]. left. apply H1. right. apply H2.
  - intro H. destruct H as [H1 | H2]. left. apply H1. right. apply H2.
Qed.

(* ================================================================= *)
(* Theorem: The power set of a set is a set *)
(* ================================================================= *)
(* Statement: forall x, exists y, forall z, z \in y <-> forall w, w \in z -> w \in x *)
(* Proof uses: power axiom *)
Theorem power_set : forall x, exists y, forall z, z \in y <-> forall w, w \in z -> w \in x.
Proof.
  intros x. apply power. intros z. split.
  - intro H. intros w H1. apply H. apply H1.
  - intro H. intros w H1. apply H. apply H1.
Qed.
