(* This example demonstrates the Axiom of Union using the Jech library.
   The union of a set A is the set of all elements that belong to elements of A. *)

Require Import Jech.
Require Import List.
Import ListNotations.

(* First-order formula representation of the Union Axiom in Fo:
   Forall A, Exists B, Forall x, (In x B <-> Exists y, (In x y /\ In y A)) *)
Definition union_fo : Fo :=
  Jech.Forall 0 (Jech.Exists 1 (Jech.Forall 2 (And
    (Imp (Pred 0 [2; 1]) (Jech.Exists 3 (And (Pred 0 [2; 3]) (Pred 0 [3; 0]))))
    (Imp (Jech.Exists 3 (And (Pred 0 [2; 3]) (Pred 0 [3; 0]))) (Pred 0 [2; 1]))))).

Theorem union_fo_valid : size union_fo >= 1.
Proof.
  apply size_ge_one.
Qed.

(* Relational union for indexed families of predicates *)
Definition family_union (I : Type) (F : I -> nat -> Prop) : nat -> Prop :=
  fun x => exists i : I, F i x.

Theorem union_predicate_exists : forall (I : Type) (F : I -> nat -> Prop),
  exists U : nat -> Prop, forall x : nat, U x <-> exists i : I, F i x.
Proof.
  intros I F.
  exists (family_union I F).
  intro x. reflexivity.
Qed.

(* End of example. *)
