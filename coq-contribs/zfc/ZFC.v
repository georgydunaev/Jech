(* ZFC.v - Definitions of basic set theory concepts and axioms of ZFC *)

Require Import MathComp.
Require Import ssreflect.

(* Definitions of basic set theory concepts *)
Definition empty_set := {}. (* The empty set *)
Definition singleton (x : Type) := {x}. (* The singleton set containing x *)
Definition pair (x y : Type) := {x, y}. (* The pair containing x and y *)

(* Axioms of ZFC *)
Axiom extensionality : forall (A B : Type), A = B <-> forall x, x in A <-> x in B.
Axiom pairing : forall (x y : Type), exists z, forall w, w in z <-> w = x \/ w = y.
Axiom union : forall (A : Type), exists B, forall x, x in B <-> exists y, x in y /\ y in A.

(* Proofs of some axioms of ZFC *)
Theorem extensionality_proof : extensionality.
Proof.
  intros A B.
  split.
    - intros H x. apply H.
    - intros H. intros x. apply H.
Qed.

Theorem pairing_proof : pairing.
Proof.
  intros x y. exists (pair x y). intros w. split.
    - intros H. destruct H as [H0 H1]. left; assumption. right; assumption.
    - intros H. destruct H as [H0 H1]. left; assumption. right; assumption.
Qed.
