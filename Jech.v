From ZFC Require Import Sets Axioms Cartesian Omega.
Require Classical_Prop Classical_Pred_Type.

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


(* TODO Определить операцию на классе и перенести её на множества. *)
(* Каждый класс, по определению, это некоторое свойство множеств. *)
(* Определение n-классов:
 0-класс - это множество.
 (n+1)-класс - это некоторое свойство n-классов.
*)

Fixpoint nclass (n:nat) := 
match n with
| 0 => Ens
| S b => (nclass b)->Prop
end.

(* 'class' is the type of well-defined classes. *)
Record class := {
 prty :> Ens->Prop;
 sound : forall (a b : Ens), EQ a b -> (prty a <-> prty b);
}.

Definition EQC (A B:class) := forall z:Ens, A z <-> B z.

(* set to class *)
Definition stoc : Ens -> class.
Proof.
intro x.
unshelve eapply Build_class.
+ intro y. exact (IN y x).
+ intros a b aeqb. split.
  - apply IN_sound_left. exact aeqb.
  - apply IN_sound_left. apply EQ_sym. exact aeqb.
Defined.

Coercion stoc : Ens >-> class.

Definition axExtC (x y:Ens) : EQ x y <-> EQC x y
 :=(axExt x y).

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
| c2 : VI false
.

Theorem theyneq : VI true <> VI false.
intros H.
pose (x1:=c1 : VI true).
pose (x2:=c2 : VI false).
replace (VI false) with (VI true) in x2.
destruct x1.

inversion x1.
change V
change 
auto.

Inductive Va:Set :=.
Inductive Vb:Set :=.

Definition ce : Ens->Prop.

(* New comprehension *)
Definition Compr : Ens -> class -> Ens.
Proof.
simple induction 1. intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
simple induction 1; intros x p; exact (f x).
Defined.

Definition nComp_sound_left x y C (H:EQ x y)
: EQ (Compr x C) (Compr y C).
Proof.
apply axExtC.
intro z. split.
+ intro a. simpl in * |- *.
  (*unfold Compr in * |- *. *)
 auto with zfc.



(* Traditional Product *)

(* We will not use these definitions.
 Soundness is not proved. They may require classical logic.
*)
Definition OrdPair (x y:Ens) := Paire (Sing x) (Paire x y).

Definition Product1 (X Y:class) (z:Ens) : Prop
:= exists (x y:Ens), (EQ z (OrdPair x y)) /\ X x /\ Y y.

Definition Product0 (x y:Ens) :=
Comp
 (Power (Power (Union (OrdPair x y))))
 (Product1 x y)
.

(* Which set (Prod X Y) belong to? It doesn't matter 
because it's already proven that (Prod X Y) is a set. *)

Definition Prod1 (X Y : class) (z:Ens) : Prop
:= exists (x y:Ens), (EQ z (Couple x y)) /\ X x /\ Y y.

Theorem Prod1_sound (x y:Ens) : Prod (fun z=> )




Section 
