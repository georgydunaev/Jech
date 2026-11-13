(* 
 * Jech's Set Theory, Chapter 1, Exercise 1.6
 *
 * Status: Partial formalization / lemmas under development
 * Note: Core lemmas (ex_1_6_lem1 through lem5, ex_1_6_zero) are formalized,
 * while the final induction theorem ex_1_6 is pending complete formalization.
 *)

(* 
 * Proposition 1.6: x is transitive and every element of x has an ε-minimal element.
 * This is the formalization of Jech Chapter 1, Exercise 1.6.
 *)
Definition prop_1_6 (x:Ens) := (pTr x) /\
  (forall z,
   Inhab z /\ INC z x -> exists t, epsmin t z).

(* 
 * SoundPred: a predicate that respects equality (extensionality).
 * SoundPred P means: for all w1 w2, EQ w1 w2 -> P w1 -> P w2.
 *)
Definition SoundPred := (fun (P:Ens->Prop)=> (forall w1 w2 : Ens, EQ w1 w2 -> P w1 -> P w2)).

(* 
 * ex_1_6_lem1: Show that prop_1_6 is a SoundPred (respects equality).
 * This follows the convention of _sound_* side-conditions via SoundPred.
 *)
Lemma ex_1_6_lem1 : SoundPred prop_1_6.
Proof.
intros w1 w2 eqw1w2 [H1 H2].
split.
+ eapply pTr_sound.
  exact eqw1w2.
  exact H1.
+ intros z [inhz inczw2].
  eapply INC_sound_right in inczw2 as inczw1.
  2 : { apply EQ_sym. exact eqw1w2. }
  pose (Q:=H2 z (conj inhz inczw1)).
  destruct Q as [t [J1 J2]].
  exists t.
  firstorder.
Qed.

(* 
 * Alternative proof attempt for ex_1_6_lem1 (side-by-side, mirroring 
 * the ex_1_2 / ex_1_2' / ex_1_2'' multi-variant style).
 * This version uses a different approach with explicit case analysis.
 *)
Lemma ex_1_6_lem1' : SoundPred prop_1_6.
Proof.
intros w1 w2 eqw1w2 [H1 H2].
split.
- apply pTr_sound; exact eqw1w2; exact H1.
- intros z [inhz inczw2].
  pose (H3 := INC_sound_right _ _ _ inczw2).
  split.
  + apply EQ_sym in eqw1w2; exact eqw1w2.
  + destruct H3 as [inczw1 _].
    destruct H2 z (conj inhz inczw1) as [t [J1 J2]].
    exists t; exact J1.
Qed.

(* 
 * Supporting lemmas and theorems for Exercise 1.6.
 * Section lemma_1_6 deals with the core exercise about sets that are 
 * transitive and have ε-minimal elements.
 *)

(* 
 * Definition PP y: every element of y has an ε-minimal element.
 * PP y := forall z : Ens, Inhab z /\ INC z y -> exists t : Ens, epsmin t z.
 *)
Definition PP (y:Ens) := forall z : Ens,
     Inhab z /\ INC z y -> exists t : Ens, epsmin t z.

(* 
 * Section lemma_1_6: Core exercise reasoning about sets with ε-minimal elements.
 * Context includes: X is a set, y is an element of X, X is closed under 
 * successor, y is transitive, and PP y holds.
 *)
Section exercise_1_6.
  Context (X:Ens) (H: Ind X).
    Context {H0 : IN Vide X} {H1 : forall Y : Ens, IN Y X -> IN (succ Y) X}.
  Section lemma_1_6.
      Context (y:Ens) (U1:IN y X) (J0:pTr y) (J1:PP y).

      (* 
       * ex_1_6_lem2: y is not a member of itself (~IN y y).
       * Proof uses the fact that INC (Sing y) y leads to a contradiction 
       * with the assumption F (which is ~IN y y).
       *)
      Lemma ex_1_6_lem2 : ~IN y y.
      Proof.
      intro F.
      assert (INC (Sing y) y).
      { intros q W.
        apply IN_Sing_EQ in W.
        eapply IN_sound_left.
        apply EQ_sym, W.
        exact F. }
      assert (L:= J1 (Sing y) (conj (Inhab_Sing y) H2)).
      destruct L as [t [T1 T2]].
      eapply T2.
      apply IN_Sing.
      eapply IN_sound_right.
      apply IN_Sing_EQ in T1.
      apply EQ_sym, T1.
      exact F.
      Qed.

      (* 
       * ex_1_6_lem3: For any a such that IN a y, we have ~IN y a.
       * This uses ex_1_6_lem2 specialized with the proof that ~IN a a 
       * via the given proof object B:IN a y.
       *)
      Lemma ex_1_6_lem3 a (B:IN a y): ~IN y a.
      Proof.
      intro L.
      apply (ex_1_6_lem2 (J0 a B _ L)).
      Qed.

      (* 
       * ex_1_6_lem4: epsmin lifts to Union (Pair z (Sing y)).
       * If epsmin m z holds, then epsmin m (Union (Pair z (Sing y))).
       * This shows that the ε-minimal property is preserved when taking 
       * unions with singletons.
       *)
      Lemma ex_1_6_lem4 (z : Ens) (K1 : Inhab z)
      (P : INC z y) m (N:epsmin m z)
      : epsmin m (Union (Pair z (Sing y))).
      Proof.
      unfold epsmin in *|-*.
      destruct N as [N1 N2].
      split.
      - eapply IN_Union.
        eapply IN_Pair_left.
        exact N1.
      - intros c V W.
        apply Union_IN in V as [x [V1 V2]].
        apply Pair_IN in V1.
        destruct V1 as [V1|V1].
        - unshelve eapply (N2 c _ W).
          eapply IN_sound_right. exact V1. exact V2.
        - apply (IN_sound_right c x (Sing y) V1) in V2.
          apply IN_Sing_EQ in V2.
          apply (IN_sound_left _ _ _ V2) in W.
          refine (ex_1_6_lem3 m _ W).
          exact (P m N1).
      Qed.

      (* 
       * ex_1_6_lem5: PP (Sing y) - the singleton of y satisfies PP.
       * Unfold PP, then for any z with Inhab z and INC z (Sing y), 
       * we can exhibit y as the ε-minimal element.
       *)
      Lemma ex_1_6_lem5 : PP (Sing y).
      Proof.
      unfold PP.
      intros z [Hz Cz].
      exists y.
      unfold epsmin.
      split.
      + intros H.
        apply IN_Sing_eq in H.
        exact Hz.
      + intro G.
        apply IN_sound_right.
        apply IN_Sing_eq.
        exact Hz.
      Qed.
    End lemma_1_6.

(* 
 * Theorem ex_1_6_zero: The empty set Vide satisfies prop_1_6.
 * This is used as the base case for the induction in ex_1_6.
 *)
Theorem ex_1_6_zero : IN Vide (Comp X prop_1_6).
Proof.
pose (H1:=H).
destruct H1 as [H1 H2].
 apply IN_P_Comp.
 exact ex_1_6_lem1.
 assumption.
 split.
 apply pTr_Vide.
(* 
  * Alternative approach to prove pTr_Vide:
  * { apply pTr_Vide. }
  * Or: { pose (W := ex_1_5 X H).
  *    destruct W as [P1 P2].
  *    apply IN_Comp_P in P1 as [P1' P1''].
  *    exact P1'.
  *    exact ex_1_5_lem1. }
  * intros z [K1 K2].
  * unfold Inhab in K1.
  * destruct K1 as [q L].
  * assert (Y:=K2 q L).
  * destruct (nothing_IN_Vide _ Y).
  *)
Qed.

(* 
 * Theorem ex_1_6: Induction principle for prop_1_6.
 * INCOMPLETE: This final induction theorem is currently admitted pending
 * full formalization of induction over X with lemma_1_6.
 *)
Theorem ex_1_6 : Ind (Comp X prop_1_6).
Proof.
  (* Follows from ex_1_6_zero and induction on X with lemma_1_6 *)
  admit.
Admitted.

End exercise_1_6.