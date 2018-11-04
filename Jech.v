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

Lemma sousym (K:Ens->Prop)
(H:forall (a b : Ens), EQ a b -> (K a -> K b))
: forall (a b : Ens), EQ a b -> (K a <-> K b).
Proof.
intros a b aeqb. split.
apply (H a b aeqb).
apply H. apply EQ_sym. exact aeqb.
Defined.

Definition EQC (A B:class) := forall z:Ens, A z <-> B z.

(* set to class *)
Definition stoc : Ens -> class.
Proof.
intro x.
unshelve eapply Build_class.
+ intro y. exact (IN y x).
+ intros a b aeqb.
  apply sousym.
  intros a0 b0 H H0.
  eapply IN_sound_left. exact H. exact H0. exact aeqb.
  (*- apply IN_sound_left. apply EQ_sym. exact aeqb.*)
Defined.

Coercion stoc : Ens >-> class.

Definition axExtC (x y:Ens) : EQ x y <-> EQC x y
 := (axExt x y).

(* New comprehension *)
Definition Compr : Ens -> class -> Ens.
Proof.
intros e c.
exact (Comp e c).
Defined.

(*Definition nComp_sound_left x y C (H:EQ x y)
: EQ (Compr x C) (Compr y C).
Proof.
apply axExtC.
intro z. split.
+ intro a. simpl in * |- *.
  (*unfold Compr in * |- *. *)
 auto with zfc.*)



(* Traditional Product *)

(* They may require classical logic. *)
(* Kuratowski construction *)
Definition OrdPair (x y : Ens) := Paire (Sing x) (Paire x y).

Theorem OrdPair_sound_left (x1 x2 y : Ens) (H : EQ x1 x2)
 : EQ (OrdPair x1 y) (OrdPair x2 y).
Proof.
unfold OrdPair.
apply EQ_tran with (E2:=Paire (Sing x1) (Paire x2 y)).
+ eapply Paire_sound_right.
  eapply Paire_sound_left.
  assumption.
+ eapply Paire_sound_left.
  eapply Sing_sound.
  assumption.
Defined.

Theorem OrdPair_sound_right (x y1 y2 : Ens) (H : EQ y1 y2)
 : EQ (OrdPair x y1) (OrdPair x y2).
Proof.
unfold OrdPair.
eapply Paire_sound_right.
eapply Paire_sound_right.
assumption.
Defined.

(* will not use this *)
Definition cProduct_ord (X Y : class) : class.
Proof.
unshelve eapply Build_class.
intro z.
exact (exists (x y:Ens), (EQ z (OrdPair x y)) /\ X x /\ Y y).
apply sousym.
intros a b aeqb e.
destruct e as [x [y [aeq [xx yy]]]].
exists x, y.
repeat split.
{ apply EQ_tran with (E2:=a).
  apply EQ_sym. exact aeqb.
  exact aeq. }
exact xx.
exact yy.
Defined.


(* will not use this *)
Definition eProduct_ord (x y:Ens) :=
Comp
 (Power (Power (Union (OrdPair x y))))
 (cProduct_ord x y)
.

(* Which set (Prod X Y) belong to? It doesn't matter 
because it's already proven that (Prod X Y) is a set. *)

Definition cProd (X Y : class) : class.
Proof.
unshelve eapply Build_class.
intro z.
exact (exists (x y:Ens), (EQ z (Couple x y)) /\ X x /\ Y y).
apply sousym.
intros a b aeqb e.
destruct e as [x [y [aeq [xx yy]]]].
exists x, y.
repeat split.
{ apply EQ_tran with (E2:=a).
  apply EQ_sym. exact aeqb.
  exact aeq. }
exact xx.
exact yy.
Defined.

(* Class of all sets *)
Definition cV : class.
Proof.
unshelve eapply Build_class.
+ intro z. exact True.
+ apply sousym. intros a b H1 H2. exact H2.
Defined.

(* Empty class *)
Definition cE : class.
Proof.
unshelve eapply Build_class.
+ intro z. exact False.
+ apply sousym. intros a b H1 H2. exact H2.
Defined.

(*_________________________________*)

(* (n+1)th power of A *)
Fixpoint cP1Pow (A:class) (n:nat) :=
match n with
 | O => A
 | S x => cProd (cP1Pow A x) A 
end.

(* Relations *)

Definition cDom (R:class) : class.
Proof.
unshelve eapply Build_class.
intro u.
exact (exists v, R (Couple u v)).
apply sousym.
intros a b aeqb H.
destruct H as [x w].
exists x.
rewrite (sound R).
exact w.
apply Couple_sound_left.
auto with zfc. (*apply EQ_sym; exact aeqb.*)
Defined.

(* "is a set" predicate on classes *)
Definition ias (s: class) : Prop.
Proof.
exact (exists (x:Ens), forall w, s w <-> IN w x).
Defined.

(* "is a set" is a sound property on classes. *)
Definition ias_sound (A B: class)
(w:EQC A B) (H:ias A): ias B.
Proof.
unfold ias in * |- *.
destruct H as [x eqv].
exists x.
intro z.
unfold EQC in w.
rewrite <- w.
apply eqv.
Defined. 
(* Proof. firstorder. (* Show Proof. *) . Defined. *)

Definition cprty_sound (cprty:class->Prop) (A B: class)
(w:EQC A B) (H:cprty A): cprty B.
Proof. unfold EQC in w. firstorder. Abort.

(* ToDo: Find unsound class property. *)
Definition cprty_unsound : exists (cprty : class->Prop) 
(A B : class) (w : EQC A B) (HA : cprty A) (HB : cprty B), False.
Proof. Abort.


(* 
Def.: Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
*)
(* Now I will define extraction of the first and the 
second element of a couple. *)

Theorem unionsing (M : Ens) : EQ (Union (Sing M)) M.
Proof.
apply axExt.
intro z; split; intro y.
+ apply Union_IN in y.
  destruct y as [w [K1 K2]].
  apply IN_Sing_EQ in K1.
  apply IN_sound_right with (E':=w); assumption.
+ unshelve eapply IN_Union.
  exact M.
  exact (IN_Sing M).
  assumption.
Defined.

Lemma unionpairvide (M : Ens) : EQ (Union (Paire Vide M)) M.
Proof.
apply axExt.
intro z; split; intro y.
+ apply Union_IN in y.
   destruct y as [w [K1 K2]].
  apply Paire_IN in K1.
   destruct K1 as [H|H].
  apply IN_sound_right with (1:=H) in K2.
  destruct (Vide_est_vide _ K2).
  apply IN_sound_right with (1:=H) in K2.
  exact K2.
+ unshelve eapply IN_Union.
  exact M.
  auto with zfc.
  assumption.
Defined.

(* First element *)
Definition Q1 : class.
Proof.
unshelve eapply Build_class.
intro z.
exact (exists x, EQ z (Sing x)).
apply sousym.
intros a b aeqb [x h].
(*split.
eapply IN_sound_left. exact aeqb. exact g.*)
exists x.
apply EQ_tran with (E2:=a); auto with zfc.
Defined.

Definition Fst (p:Ens) := Union (Union (Comp p Q1)).

(* Micro Sermon: Mindless proof-hacking is a terrible temptation...
Try to resist! *)
Theorem Comp_elim x y (K:class) : IN x (Comp y K) -> (IN x y /\ K x).
Proof.
intro e.
split.
+ exact ((Comp_INC y K) _ e).
+ apply IN_Comp_P in e. exact e.
  intros.
  rewrite <- (sound K).
  exact H.
  exact H0.
Defined.

Lemma SingEqPair x y1 y2 (J: EQ (Sing x) (Paire y1 y2)) :
EQ x y1 /\ EQ x y2.
Proof.
apply EQ_sym in J.
pose (i1:=IN_Paire_left y1 y2).
apply IN_sound_right with (1:=J) in i1.
apply IN_Sing_EQ, EQ_sym in i1.
pose (i2:=IN_Paire_right y1 y2).
apply IN_sound_right with (1:=J) in i2.
apply IN_Sing_EQ, EQ_sym in i2.
split; assumption.
Defined.

Theorem Fst_eq_OLD  a b : EQ (Fst (Couple a b)) a.
Proof.
unfold Fst.
apply axExt; intro z; split; intro y.
+ apply Union_IN in y as [w1 [w2 w3]].
  apply Union_IN in w2 as [v1 [v2 v3]].
  apply Comp_elim in v2 as [u1 u2].
  apply Paire_IN in u1 as [H1|H2].
  - apply IN_sound_right with (1:=H1) in v3.
    apply IN_Sing_EQ in v3.
    apply IN_sound_right with (1:=v3) in w3.
    exact w3.
  - apply IN_sound_right with (1:=H2) in v3.
    apply Paire_IN in v3 as [L1|L2].
    * apply IN_sound_right with (1:=L1) in w3.
      destruct (Vide_est_vide z w3).
    * destruct u2 as [t1 t2].
      apply EQ_sym in t2.
      apply EQ_tran with (2:=H2) in t2.
      apply SingEqPair in t2 as [u1 u2].
      apply IN_sound_right with (1:=L2) in w3.
      apply EQ_sym in u2.
      apply IN_sound_right with (1:=u2) in w3.
      apply IN_sound_right with (1:=u1) in w3.
      destruct (Vide_est_vide _ w3) as [].
+ apply IN_Union with (E':=a).
  2 : assumption.
  apply IN_Union with (E':=Sing a).
  2 : auto with zfc.
  apply IN_P_Comp.
  { intros w1 w2 qw1 ew1w2.
    rewrite (sound Q1). exact qw1. apply EQ_sym; assumption. }
  unfold Couple. auto with zfc.
  simpl (prty Q1). cbv beta. exists a. apply EQ_refl.
Defined.

Theorem Fst_eq_lem1  a b : EQ (Comp (Couple a b) Q1) (Sing (Sing a)).
Proof.
apply axExt; intro z; split; intro v2.
+ apply Comp_elim in v2 as [u1 u2].
  apply Paire_IN in u1 as [H1|H2].
  apply IN_sound_left with (1:=(EQ_sym _ _ H1)).
  auto with zfc.
  destruct u2 as [t1 t2].
      apply EQ_sym in t2.
      apply EQ_tran with (2:=H2) in t2.
  apply SingEqPair in t2 as [u1 u2].
      apply EQ_sym in u2.
  pose (FF:=EQ_tran _ _ _ u2 u1).
  pose (u:=IN_Sing b).
      apply IN_sound_right with (1:=FF) in u.
      destruct (Vide_est_vide _ u) as [].
+ apply IN_P_Comp.
  { intros w1 w2 qw1 ew1w2.
    rewrite (sound Q1). exact qw1. apply EQ_sym; assumption. }
  apply IN_Sing_EQ in v2.
  apply IN_sound_left with (E:=Sing a).
  auto with zfc.
  unfold Couple. auto with zfc.
  simpl (prty Q1). cbv beta. exists (a).
  apply IN_Sing_EQ; assumption.
Defined.

Theorem sing2union W M : EQ W (Sing M) -> EQ (Union W) M.
Proof. intro H. pose (y:= unionsing M).
apply EQ_tran with (E2:=Union (Sing M)).
apply Union_sound. assumption.
assumption.
Defined.

Theorem Fst_eq  a b : EQ (Fst (Couple a b)) a.
Proof.
unfold Fst.
repeat apply sing2union.
apply Fst_eq_lem1.
Defined.

Definition Q2 : class.
Proof.
unshelve eapply Build_class.
intro z.
exact (exists x, EQ z (Paire Vide (Sing x))).
apply sousym.
intros a b aeqb [x h].
exists x.
apply EQ_tran with (E2:=a); auto with zfc.
Defined.

Definition Snd0 (p:Ens) := Union (Union (Comp p Q2)).
Definition Snd (p:Ens) := Union (Union (Comp p Q2)).

Theorem Snd_eq  a b : EQ (Snd (Couple a b)) b.
Proof.
unfold Fst.
apply axExt; intro z; split; intro y.
+ apply Union_IN in y as [w1 [w2 w3]].
  apply Union_IN in w2 as [v1 [v2 v3]].
  (* to be continued *)
Abort.

(* I am adapting Jech's definitions to Couple of the library.*)
Theorem  domias (R:class) (w : ias R) : (ias (cDom R)).
Proof.
unfold ias in *|-*.
Abort.

(* Functions *)

(*pose (i:=IN_Sing x).
enough (forall x z, (IN z (Sing x)) <-> (EQ z x)).*)
