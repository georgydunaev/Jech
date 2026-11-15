(* 
 * Jech's Set Theory, Chapter 1, Exercise 1.6
 *
 * Status: Complete self-contained formalization
 * Core lemmas (ex_1_6_lem1 through lem5, ex_1_6_zero) and the main induction
 * theorem ex_1_6 are fully formalized and proved without admit.
 *)

(* Prelude declarations for the Aczel-Werner Ens universe *)
Parameter Ens : Type.
Parameter EQ : Ens -> Ens -> Prop.
Parameter IN : Ens -> Ens -> Prop.

Definition INC (x y : Ens) : Prop := forall z : Ens, IN z x -> IN z y.
Definition Inhab (x : Ens) : Prop := exists z : Ens, IN z x.
Definition pTr (x : Ens) : Prop := forall y : Ens, IN y x -> INC y x.
Definition epsmin (t z : Ens) : Prop := IN t z /\ forall c : Ens, IN c z -> ~ IN c t.

Parameter Vide : Ens.
Parameter Sing : Ens -> Ens.
Parameter Pair : Ens -> Ens -> Ens.
Parameter Union : Ens -> Ens.
Parameter succ : Ens -> Ens.
Parameter Comp : Ens -> (Ens -> Prop) -> Ens.

Definition Ind (X : Ens) : Prop :=
  IN Vide X /\ (forall Y : Ens, IN Y X -> IN (succ Y) X).

Axiom EQ_refl : forall x : Ens, EQ x x.
Axiom EQ_sym : forall x y : Ens, EQ x y -> EQ y x.
Axiom IN_sound_left : forall x1 x2 y : Ens, EQ x1 x2 -> IN x1 y -> IN x2 y.
Axiom IN_sound_right : forall x y1 y2 : Ens, EQ y1 y2 -> IN x y1 -> IN x y2.
Axiom INC_sound_right : forall x y1 y2 : Ens, EQ y1 y2 -> INC x y1 -> INC x y2.
Axiom pTr_sound : forall w1 w2 : Ens, EQ w1 w2 -> pTr w1 -> pTr w2.
Axiom nothing_IN_Vide : forall x : Ens, IN x Vide -> False.
Axiom pTr_Vide : pTr Vide.
Axiom IN_Sing : forall x : Ens, IN x (Sing x).
Axiom IN_Sing_EQ : forall x y : Ens, IN x (Sing y) -> EQ x y.
Axiom Inhab_Sing : forall x : Ens, Inhab (Sing x).
Axiom IN_Pair_left : forall x y : Ens, IN x (Pair x y).
Axiom Pair_IN : forall x y z : Ens, IN z (Pair x y) -> EQ z x \/ EQ z y.
Axiom IN_Union : forall x y z : Ens, IN y z -> IN x y -> IN x (Union z).
Axiom Union_IN : forall z x : Ens, IN x (Union z) -> exists y : Ens, IN y z /\ IN x y.
Axiom IN_Succ_or : forall y z : Ens, IN z (succ y) -> EQ z y \/ IN z y.
Axiom IN_Succ_in : forall y z : Ens, IN z y -> IN z (succ y).
Axiom IN_Succ_self : forall y : Ens, IN y (succ y).
Axiom Comp_INC : forall (X : Ens) (P : Ens -> Prop) (z : Ens), IN z (Comp X P) -> IN z X.
Axiom IN_Comp_P : forall (X : Ens) (P : Ens -> Prop) (z : Ens),
  (forall w1 w2 : Ens, EQ w1 w2 -> P w1 -> P w2) ->
  IN z (Comp X P) -> P z.
Axiom IN_P_Comp : forall (X : Ens) (P : Ens -> Prop) (z : Ens),
  (forall w1 w2 : Ens, EQ w1 w2 -> P w1 -> P w2) ->
  IN z X -> P z -> IN z (Comp X P).
Axiom classic_inhab : forall P : Prop, P \/ ~ P.

(* 
 * Proposition 1.6: x is transitive and every element of x has an epsilon-minimal element.
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
- eapply pTr_sound; [exact eqw1w2 | exact H1].
- intros z [inhz inczw2].
  assert (inczw1 : INC z w1).
  { eapply INC_sound_right; [apply EQ_sym; exact eqw1w2 | exact inczw2]. }
  destruct (H2 z (conj inhz inczw1)) as [t [J1 J2]].
  exists t; split; [exact J1 | exact J2].
Qed.

(* 
 * Supporting lemmas and theorems for Exercise 1.6.
 * Section lemma_1_6 deals with the core exercise about sets that are 
 * transitive and have epsilon-minimal elements.
 *)

(* 
 * Definition PP y: every non-empty subset of y has an epsilon-minimal element.
 * PP y := forall z : Ens, Inhab z /\ INC z y -> exists t : Ens, epsmin t z.
 *)
Definition PP (y:Ens) := forall z : Ens,
     Inhab z /\ INC z y -> exists t : Ens, epsmin t z.

(* 
 * Section lemma_1_6: Core exercise reasoning about sets with epsilon-minimal elements.
 * Context includes: X is a set, y is an element of X, X is closed under 
 * successor, y is transitive, and PP y holds.
 *)
Section exercise_1_6.
  Context (X:Ens) (H: Ind X).
  Section lemma_1_6.
      Context (y:Ens) (U1:IN y X) (J0:pTr y) (J1:PP y).

      (* 
       * ex_1_6_lem2: y is not a member of itself (~IN y y).
       * Proof uses the fact that INC (Sing y) y leads to a contradiction 
       * with the assumption F (which is IN y y).
       *)
      Lemma ex_1_6_lem2 : ~IN y y.
      Proof.
      intro F.
      assert (H2 : INC (Sing y) y).
      { intros q W.
        apply IN_Sing_EQ in W.
        eapply IN_sound_left.
        apply EQ_sym, W.
        exact F. }
      assert (L:= J1 (Sing y) (conj (Inhab_Sing y) H2)).
      destruct L as [t [T1 T2]].
      eapply (T2 y).
      - apply IN_Sing.
      - eapply IN_sound_right.
        + apply IN_Sing_EQ in T1.
          apply EQ_sym, T1.
        + exact F.
      Qed.

      (* 
       * ex_1_6_lem3: For any a such that IN a y, we have ~IN y a.
       * This uses ex_1_6_lem2 specialized with the proof that ~IN a a 
       * via the given proof object B:IN a y.
       *)
      Lemma ex_1_6_lem3 a (B:IN a y): ~IN y a.
      Proof.
      intro L.
      apply (ex_1_6_lem2 (J0 a B y L)).
      Qed.

      (* 
       * ex_1_6_lem4: epsmin lifts to Union (Pair z (Sing y)).
       * If epsmin m z holds, then epsmin m (Union (Pair z (Sing y))).
       * This shows that the epsilon-minimal property is preserved when taking 
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
        + eapply IN_Pair_left.
        + exact N1.
      - intros c V W.
        apply Union_IN in V as [x [V1 V2]].
        apply Pair_IN in V1.
        destruct V1 as [V1|V1].
        + apply (N2 c).
          * eapply IN_sound_right; [exact V1 | exact V2].
          * exact W.
        + assert (V2' : IN c (Sing y)).
          { eapply IN_sound_right; [exact V1 | exact V2]. }
          apply IN_Sing_EQ in V2'.
          assert (W' : IN y m).
          { eapply IN_sound_left; [exact V2' | exact W]. }
          exact (ex_1_6_lem3 m (P m N1) W').
      Qed.

      (* 
       * ex_1_6_lem5: PP (Sing y) - the singleton of y satisfies PP.
       * Unfold PP, then for any z with Inhab z and INC z (Sing y), 
       * we can exhibit y as the epsilon-minimal element.
       *)
      Lemma ex_1_6_lem5 : PP (Sing y).
      Proof.
      unfold PP.
      intros z [[q Hqz] Cz].
      exists y.
      unfold epsmin.
      assert (Heq_qy : EQ q y).
      { apply IN_Sing_EQ. exact (Cz q Hqz). }
      split.
      + eapply IN_sound_left; [exact Heq_qy | exact Hqz].
      + intros c Hcz Hcy.
        assert (Heq_cy : EQ c y).
        { apply IN_Sing_EQ. exact (Cz c Hcz). }
        apply ex_1_6_lem2.
        eapply IN_sound_left; [exact Heq_cy | exact Hcy].
      Qed.

      Lemma pTr_succ : pTr (succ y).
      Proof.
      intros u Hu w Hwu.
      apply IN_Succ_or in Hu.
      destruct Hu as [Heq_uy | Hin_uy].
      - apply IN_Succ_in.
        eapply IN_sound_right; [exact Heq_uy | exact Hwu].
      - apply IN_Succ_in.
        exact (J0 u Hin_uy w Hwu).
      Qed.

      Lemma PP_succ : PP (succ y).
      Proof.
      intros z [Hz Hinc].
      assert (Hsound_in_y : forall w1 w2 : Ens, EQ w1 w2 -> IN w1 y -> IN w2 y).
      { intros w1 w2 Heq Hw1. eapply IN_sound_left; [exact Heq | exact Hw1]. }
      destruct (classic_inhab (Inhab (Comp z (fun w => IN w y)))) as [Hinh | Hempty].
      - assert (Hsub : INC (Comp z (fun w => IN w y)) y).
        { intros w Hw. exact (IN_Comp_P z (fun u => IN u y) w Hsound_in_y Hw). }
        destruct (J1 (Comp z (fun w => IN w y)) (conj Hinh Hsub)) as [m [Hm1 Hm2]].
        exists m. split.
        + exact (Comp_INC z (fun u => IN u y) m Hm1).
        + intros c Hcz Hcm.
          assert (Hc_succ : IN c (succ y)) by exact (Hinc c Hcz).
          apply IN_Succ_or in Hc_succ.
          destruct Hc_succ as [Heq_cy | Hin_cy].
          * assert (Hm_y : IN m y) by exact (IN_Comp_P z (fun u => IN u y) m Hsound_in_y Hm1).
            apply (ex_1_6_lem3 m Hm_y).
            eapply IN_sound_left; [exact Heq_cy | exact Hcm].
          * apply (Hm2 c).
            -- exact (IN_P_Comp z (fun u => IN u y) c Hsound_in_y Hcz Hin_cy).
            -- exact Hcm.
      - assert (Hz_sing : INC z (Sing y)).
        { intros w Hw.
          assert (Hw_succ : IN w (succ y)) by exact (Hinc w Hw).
          apply IN_Succ_or in Hw_succ.
          destruct Hw_succ as [Heq_wy | Hin_wy].
          - eapply IN_sound_left; [apply EQ_sym; exact Heq_wy | apply IN_Sing].
          - exfalso. apply Hempty. exists w.
            exact (IN_P_Comp z (fun u => IN u y) w Hsound_in_y Hw Hin_wy). }
        exact (ex_1_6_lem5 z (conj Hz Hz_sing)).
      Qed.
    End lemma_1_6.

(* 
 * Theorem ex_1_6_zero: The empty set Vide satisfies prop_1_6.
 * This is used as the base case for the induction in ex_1_6.
 *)
Theorem ex_1_6_zero : IN Vide (Comp X prop_1_6).
Proof.
destruct H as [H1 H2].
apply IN_P_Comp.
- exact ex_1_6_lem1.
- exact H1.
- split.
  + apply pTr_Vide.
  + intros z [[q L] K2].
    assert (Y := K2 q L).
    destruct (nothing_IN_Vide q Y).
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
 * Complete formalization of induction over X with lemma_1_6.
 *)
Theorem ex_1_6 : Ind (Comp X prop_1_6).
Proof.
  split.
  - exact ex_1_6_zero.
  - intros y Hy.
    assert (HyX : IN y X) by exact (Comp_INC X prop_1_6 y Hy).
    assert (Hprop : prop_1_6 y) by exact (IN_Comp_P X prop_1_6 y ex_1_6_lem1 Hy).
    destruct Hprop as [J0 J1].
    apply IN_P_Comp.
    + exact ex_1_6_lem1.
    + destruct H as [_ Hsucc]. exact (Hsucc y HyX).
    + split.
      * exact (pTr_succ y J0).
      * exact (PP_succ y J0 J1).
Qed.

End exercise_1_6.
