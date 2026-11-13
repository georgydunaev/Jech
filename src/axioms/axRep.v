(* ========================================================================= *)
(*  axRep.v — Axiom of Replacement formalization with sup constructor        *)
(*                                                                           *)
(*  Constructs the replacement image set using the sup constructor           *)
(*  leveraging impredicative comprehension.                                  *)
(* ========================================================================= *)

Parameter Ens : Type.
Parameter EQ : Ens -> Ens -> Prop.
Parameter IN : Ens -> Ens -> Prop.
Parameter sup : forall (A : Type), (A -> Ens) -> Ens.

Axiom EQ_refl : forall x : Ens, EQ x x.
Axiom IN_sup : forall (A : Type) (f : A -> Ens) (z : Ens),
  (IN z (sup A f) <-> exists a : A, EQ z (f a)).

Theorem axRep_image : forall (A : Type) (f : A -> Ens),
  exists C : Ens, forall a : A, IN (f a) C.
Proof.
  intros A f.
  exists (sup A f).
  intro a.
  apply IN_sup.
  exists a.
  apply EQ_refl.
Qed.
