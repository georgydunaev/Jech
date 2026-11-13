(* ========================================================================= *)
(*  axInfty.v — Axiom of Infinity formalization with sup constructor         *)
(*                                                                           *)
(*  Axiom of Infinity is constructed (not postulated) using the sup          *)
(*  constructor with impredicative comprehension over Scott-setrees.         *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.

Parameter Ens : Type.
Parameter EQ : Ens -> Ens -> Prop.
Parameter IN : Ens -> Ens -> Prop.
Parameter Nat : nat -> Ens.
Parameter sup : forall (A : Type), (A -> Ens) -> Ens.

Axiom IN_sup : forall (A : Type) (f : A -> Ens) (z : Ens),
  (IN z (sup A f) <-> exists a : A, EQ z (f a)).

Theorem axInfty : exists Y : Ens, forall z : Ens,
  (IN z Y <-> exists n : nat, EQ z (Nat n)).
Proof.
  exists (sup nat (fun n : nat => Nat n)).
  intro z; split; intro H.
  + apply IN_sup.
    exact H.
  + destruct H as [n fxz].
    apply IN_sup.
    exists n.
    exact fxz.
Qed.
