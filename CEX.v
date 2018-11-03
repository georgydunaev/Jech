From ZFC Require Import Sets Axioms Cartesian Omega.
(*
Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.

Definition EQ : Ens -> Ens -> Prop.
Proof.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, exists y : B, eq1 x (g y)).
exact (forall y : B, exists x : A, eq1 x (g y)).
Defined.

Definition Vide:Ens := sup False (fun k=>match k with end).
*)
Definition S1 := sup unit (fun k=>match k with | _ => Vide end).
Definition S2 := sup bool (fun k=>match k with | _ => Vide end).


Definition id {T} := fun x : T => x.
 
Lemma exists_bijection (A B:Type):
A = B -> exists f, exists g, forall (x:A) (y:B),
 f x = y -> g y = x.
Proof.
 intro H; subst.
 exists id.
 exists id.
 intros. subst.
 reflexivity.
Defined.

Lemma unit_neq_bool: (bool:Type) = (unit:Type) -> False.
Proof.
intro Heq.
destruct (exists_bijection bool unit Heq) as [f [g Hfg]].
destruct (f true) eqn: Hft.
destruct (f false) eqn: Hff.
pose proof (Hfg _ _ Hft) as Hgtt.
pose proof ( Hfg _ _ Hff) as Hgtf.
rewrite Hgtf in Hgtt.
inversion Hgtt.
Defined.

Theorem uneb : S1 <> S2.
Proof.
intro H.
unfold S1,S2 in H.
inversion H.
symmetry in H1.
exact (unit_neq_bool H1).
Defined.


Theorem axExt : forall x y : Ens,
   EQ x y <-> forall z, (IN z x <-> IN z y).
Proof.
intros.
split.
+ intros.
  split.
  - apply IN_sound_right. exact H.
  - apply IN_sound_right. apply EQ_sym. exact H.
+ induction x as [A f], y as [B g].
  intro K.
  simpl in * |- *.
  split.
  - intro x.
    apply K.
    exists x.
    apply EQ_refl.
  - intro y.
    assert (Q:EXType B (fun y0 : B => EQ (g y) (g y0))).
    * exists y.
      apply EQ_refl.
    * destruct (proj2 (K (g y)) Q).
      exists x.
      apply EQ_sym.
      exact H0.
Defined.

Theorem ESS : EQ S1 S2.
Proof.
apply axExt.
simpl.
intro z.
split.
+ intro a.
  exists true.
  destruct a.
  exact H.
+ intro a.
  exists tt.
  destruct a.
  exact H.
Defined.
(* We have: S1<>S2, but (EQ S1 S2).
c1 extracts S1 from the pair.
c2 extracts S2 from the pair.
*)

Definition EQC (A B:Ens -> Prop) := forall z:Ens, A z <-> B z.


(*Definition Comp : Ens -> (Ens -> Prop) -> Ens.*)
Definition Comp_not_sound_right : exists x c1 c2 (H:EQC c1 c2),
~ (EQ (Comp x c1) (Comp x c2)).

(*=====================END========================*)


(* The following is a mistake... *)
Definition Comp_not_sound_left : exists x1 x2 (H:EQ x1 x2) c,
~ (EQ (Comp x1 c) (Comp x2 c)).
Proof.
exists (Paire S1 S2).
exists (Paire S1 S2).
unshelve eapply ex_intro.
apply EQ_refl.
unshelve eapply ex_intro.
intro e.
Abort.
(*
exists S1.
exists S2.
exists ESS.
unshelve eapply ex_intro.
intro e.

assert (J: IN e S1). admit.
simpl in J. destruct J as [j1 j2].

exact (e=S1).
auto with zfc.

unfold EQ.

auto.
eq
False
I:True
  unit
  bool*)
