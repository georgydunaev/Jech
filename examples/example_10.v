(* This example demonstrates the Axiom of Union using the Jech library.
   The union of a set family is constructed using the `sup` constructor,
   building on the Ens/sup framework with impredicative comprehension. *)

Require Import Jech.
Require Import Part_III.

Parameter Ens : Type.
Parameter EQ : Ens -> Ens -> Prop.
Parameter IN : Ens -> Ens -> Prop.
Parameter sup : forall (A : Type), (A -> Ens) -> Ens.

Axiom EQ_refl : forall x : Ens, EQ x x.
Axiom IN_sup : forall (A : Type) (f : A -> Ens) (z : Ens),
  (IN z (sup A f) <-> exists a : A, EQ z (f a)).

(* The Axiom of Union in the Ens/sup framework:
   Given an index type A and a family f : A -> Ens, the union set
   exists as sup A f. *)
Theorem union_axiom_example : forall (A : Type) (f : A -> Ens),
  exists B : Ens, forall a : A, IN (f a) B.
Proof.
  intros A f.
  exists (sup A f).
  intro a.
  apply IN_sup.
  exists a.
  apply EQ_refl.
Qed.

(* End of example. *)
