Require Import Setoid.
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
Proof.
exists (Paire S1 S2).
(* Надо некорректно определить класс *)
Check fun x:Ens=> x = S1.

exists (fun x=> EQ x S1).
exists (fun x=> EQ x S2).
(*unshelve eapply ex_intro. firstorder.
intros H.
rewrite -> axExt in H.*)

(* almost
exists (Sing S1).
exists (fun x=>EQ x S1).
exists (fun x=>EQ x S2).
unshelve eapply ex_intro.
+ unfold EQC. intro z. split.
  - intro u. apply (EQ_tran _ _ _ u ESS).
  - intro u. refine (EQ_tran _ _ _ u _). apply EQ_sym. exact ESS.
+ intro H.*)
Abort.

Section sou.
Context (c1 c2 : Ens->Prop).
Context (c1_sou : forall x y, EQ x y -> (c1 x <-> c1 y)).
Context (c2_sou : forall x y, EQ x y -> (c2 x <-> c2 y)).
Definition Comp_sound_right : forall x (H:EQC c1 c2),
 (EQ (Comp x c1) (Comp x c2)).
Proof.
intros.
apply axExt.
intro z. split.
+ intro q.
  unshelve eapply IN_P_Comp.  (* c2 := (fun w=>S1=w) *)
  { unfold EQC in H.
    intros w1 w2 H0 H1.
    eapply c2_sou.
    apply EQ_sym. exact H1.
    exact H0. }
  { pose (m:= Comp_INC x c1).
    unfold INC in m.
    apply m. exact q. }
  {
    eapply IN_Comp_P in q.
    eapply H. exact q.
    intros w1 w2 H0 H1.
    eapply c1_sou. apply EQ_sym. exact H1. exact H0.
  }
+ intro q.
  unshelve eapply IN_P_Comp.
  { unfold EQC in H.
    intros w1 w2 H0 H1.
    eapply c1_sou.
    apply EQ_sym. exact H1.
    exact H0. }
  { pose (m:= Comp_INC x c2).
    unfold INC in m.
    apply m. exact q. }
  {
    eapply IN_Comp_P in q.
    eapply H. exact q.
    intros w1 w2 H0 H1.
    eapply c2_sou. apply EQ_sym. exact H1. exact H0.
  }
Defined.
End sou.

(*=====================END========================*)

(* The following is a mistake... *)
Definition Comp_not_sound_left : exists x1 x2 (H:EQ x1 x2) c,
~ (EQ (Comp x1 c) (Comp x2 c)).
Proof.
exists (Sing S1).
exists (Sing S2).
unshelve eapply ex_intro.
 apply Sing_sound; exact ESS.
exists (fun w=>S1=w).
intro Y.
rewrite axExt in Y.
pose (ys := Y S1).
destruct ys.
assert (Q:IN S1 (Comp (Sing S1) (fun w : Ens => S1 = w))).
eapply IN_P_Comp.
(* Nothing can be done *)
(*exists (Paire S1 S2).
exists (Paire S1 S2).
unshelve eapply ex_intro.
apply EQ_refl.*)
Abort.
(*___________________________________________________*)

(** INTERESTING 

Module ClassicalEns.
Import Classical_Prop.
Import Classical_Pred_Type.
(*
Definition ce :  False.
remember (classic False).
clear Heqo.
destruct o.
pose (Q:=classic False).
destruct Q.
Theorem or_elim (A B C:Prop): (A->C) ->(B->C)->((A\/B)->C).
intros.
destruct H1.
or
*)

(*N z x*)
Check Comp Omega.
Print Comp.
(*
Definition Comp : Ens -> (Ens -> Prop) -> Ens.
simple induction 1; intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
simple induction 1; intros x p; exact (f x).
Defined.
*)
(* Тут должен быть пример функции, дающей разные значения на
   на двух неравных, экстенсионально равных множествах.
   Определим два типа с нулём элементов.
*)

Inductive VI : bool -> Set :=
| c1 : VI true
.

Theorem theyneq : VI true <> VI false.
Proof.
intros H.
(*pose (x2:=c2 : VI true).*)
pose (x1:=c1 : VI true).
replace (VI true) with (VI false) in x1.
inversion x1.
Defined.

Inductive Va:Set :=.
Inductive Vb:Set :=.

Definition ce : Ens->Prop.

(*___________________________________________________*)
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
**)