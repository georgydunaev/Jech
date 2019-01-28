(****
This file is just a theorems about Couple.
****)
(* 
Def.: Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
*)

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
+ apply IN_Sing_EQ in v2.
  apply IN_P_Comp.
  { intros w1 w2 qw1 ew1w2.
    rewrite (sound Q1). exact qw1. apply EQ_sym; assumption. }
  apply IN_sound_left with (E:=Sing a).
  auto with zfc.
  unfold Couple. auto with zfc.
  simpl (prty Q1). cbv beta. exists a.
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
(*Definition Snd0 (p:Ens) := Union (Union (Comp p Q2)).*)

Definition Snd (p:Ens) := Union (Union (Comp p Q2)).

Lemma pairneqsin X Y (H: EQ (Paire Vide (Sing X)) (Sing Y) ): False.
Proof.
apply EQ_sym in H.
apply SingEqPair in H as [H1 H2].
apply EQ_sym in H2.
pose (g := EQ_tran _ _ _ H2 H1).
apply not_EQ_Sing_Vide in g as [].
Defined.

Theorem Snd_eq_lem1  a b : 
 EQ (Comp (Couple a b) Q2) (Sing (Paire Vide (Sing b))).
Proof.
apply axExt; intro z; split; intro v2.
+ apply Comp_elim in v2 as [u1 u2].
  apply Paire_IN in u1 as [H1|H2].
  destruct u2 as [t1 t2].
  apply EQ_sym in t2.
  pose (FF:=EQ_tran _ _ _ t2 H1).
  apply pairneqsin in FF as [].
  apply EQ_sym in H2.
  apply IN_sound_left with (1:=H2).
  apply IN_Sing.
+ apply IN_Sing_EQ in v2.
  apply IN_P_Comp.
  { intros w1 w2 qw1 ew1w2.
    rewrite (sound Q2). exact qw1. apply EQ_sym; assumption. }
  apply IN_sound_left with (E:=(Paire Vide (Sing b))).
  auto with zfc.
  unfold Couple. auto with zfc.
  simpl (prty Q1). cbv beta. exists b.
  assumption.
Defined.

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