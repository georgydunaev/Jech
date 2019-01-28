

Section OBSOLETE.
Import Classical_Prop Classical_Pred_Type.
Theorem OrdPair_inj_left :
 forall a b c d : Ens, EQ (OrdPair a b) (OrdPair c d)->(EQ a c/\EQ b d).
Proof.
unfold OrdPair in |- *.
intros.
  assert (e2 : EQ (Paire (Sing a) (Paire a a)) 
                  (Sing  (Sing a)) ).
   repeat apply Paire_sound_right. apply EQ_refl.
destruct (classic (EQ a b)).
+ assert (e1 : EQ (Paire (Sing a) (Paire a b)) 
                  (Paire (Sing a) (Paire a a))).
   repeat apply Paire_sound_right. apply EQ_sym; assumption.

  assert (e3 := EQ_tran _ _ _ e1 e2).
  assert (e4 := EQ_tran _ _ _ (EQ_sym _ _ e3 ) H).
(*assert (j: EQ (Sing (Sing a)) (Paire (Sing c) (Paire c d))).
apply Paire_sound.*)
  apply SingEqPair in e4 as [H1 H2].
  (*apply SingEqPair in H1 as [Ha1 Ha2].*)
  apply SingEqPair in H2 as [P1 P2].
  split. assumption. apply EQ_tran with (E2:=a). apply EQ_sym, H0.
  apply P2.
+ assert (e1: IN (Paire c d) (Paire (Sing c) (Paire c d))).
   auto with zfc.
  apply IN_sound_right with (1:=EQ_sym _ _ H) in e1.
  apply Paire_IN in e1 as [A1|A2].
  - apply EQ_sym , SingEqPair in A1 as [B1 B2].
  split. exact B1.
  assert (e23:EQ (Paire (Sing c) (Paire c d)) (Paire (Sing a) (Paire a a))).
   apply Paire_sound.
   apply Sing_sound, EQ_sym, B1.
   apply Paire_sound; apply EQ_sym; assumption.
  assert(K:=EQ_tran _ _ _ e23 e2).
  assert(R:=EQ_tran _ _ _ H K). apply EQ_sym in R.
  apply SingEqPair in R as [R1 R2].
  apply SingEqPair in R2 as [R2 R3].
  destruct (H0 R3).
 - apply Paire_EQ_cases in A2 as [[q1|q2] [q3|q4]].
(* [v1 v2].
   destruct (classic (EQ a c)).
   split. assumption.
   destruct (classic (EQ b d)).
   
  - 
apply Paire_IN in A2 as [B1|B2].
(*  assert (e2: EQ (Paire (Sing c) (Paire c d)) (Paire (Sing a) (Paire c d))).
  apply Paire_sound_left.
  apply Sing_sound, EQ_sym, B1.
  assert (e3: EQ (Paire (Sing a) (Paire c d)) (Paire (Sing a) (Paire a a))).
*)

  apply Sing_sound. EQ_sym, B1.
unshelve eapply EQ_tran (E2:=) in H.
!!!
apply EQ_tran
apply axExt; intro z; split; intro q.
 simpl in |- *. *)
 Abort.
End OBSOLETE.