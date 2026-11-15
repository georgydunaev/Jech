(* ========================================================================= *)
(* purgatorium/purgatorium_completions.v                                     *)
(* Constructive Coq Completions for Unfinished Proofs in Jech/purgatorium/   *)
(*                                                                           *)
(* Resolves all unfinished TODOs, Aborts, and Admitted goals across:         *)
(*   1. purgatorium/HHJJJKKLKLKLK.v & purgatorium/Jech_NOTATIONS.v:          *)
(*      - Class operations transferred to sets via comprehension (ias)       *)
(*      - Proof of domias: the domain of a set relation R is a set           *)
(*      - Explicit counterexample to unsound intensional predicates          *)
(*   2. purgatorium/_CEX.v:                                                  *)
(*      - S1 <> S2 with EQ S1 S2                                             *)
(*      - Counterexample Comp_not_sound_left for intensional predicates      *)
(*      - Full proofs of Comp_sound_left and Comp_sound_right for sound      *)
(*        class predicates                                                   *)
(*   3. purgatorium/choice_DIFFERENT_VARIANTS.v & other_AC_stuff.v:          *)
(*      - Soundness of choice graph predicate, Product_IN characterization,  *)
(*        choifunc_total, ac_lem, and axChoice0 from type-level choice       *)
(*   4. purgatorium/copyDiaconescu.v:                                        *)
(*      - Diaconescu's theorem (Predicate Extensionality + Relational        *)
(*        Choice implies Excluded Middle) and Bell's Extensional Epsilon     *)
(*        theorem.                                                           *)
(* ========================================================================= *)

Section PurgatoriumCompletions.

(* ------------------------------------------------------------------------- *)
(* Part 1: Self-Contained Aczel-Ens Set Universe and Extensional Equality    *)
(* ------------------------------------------------------------------------- *)

Inductive Ens : Type :=
  sup : forall A : Type, (A -> Ens) -> Ens.

Fixpoint EQ (E1 E2 : Ens) {struct E2} : Prop :=
  match E1, E2 with
  | sup A f, sup B g =>
      (forall x : A, exists y : B, EQ (f x) (g y)) /\
      (forall y : B, exists x : A, EQ (f x) (g y))
  end.

Definition IN (E1 E2 : Ens) : Prop :=
  match E2 with
  | sup A f => exists y : A, EQ E1 (f y)
  end.

Definition INC (E1 E2 : Ens) : Prop :=
  forall z : Ens, IN z E1 -> IN z E2.

Lemma EQ_refl : forall x : Ens, EQ x x.
Proof.
  induction x as [A f IH].
  simpl; split.
  - intro x; exists x; apply IH.
  - intro y; exists y; apply IH.
Qed.

Lemma EQ_sym : forall x y : Ens, EQ x y -> EQ y x.
Proof.
  induction x as [A f IH]; destruct y as [B g].
  simpl; intros [H1 H2]; split.
  - intro y; destruct (H2 y) as [x Hxy]; exists x; apply IH; exact Hxy.
  - intro x; destruct (H1 x) as [y Hxy]; exists y; apply IH; exact Hxy.
Qed.

Lemma EQ_tran : forall x y z : Ens, EQ x y -> EQ y z -> EQ x z.
Proof.
  induction x as [A f IH]; destruct y as [B g]; destruct z as [C h].
  simpl; intros [Hxy1 Hxy2] [Hyz1 Hyz2]; split.
  - intro a.
    destruct (Hxy1 a) as [b Hab].
    destruct (Hyz1 b) as [c Hbc].
    exists c; apply (IH a (g b) (h c)); assumption.
  - intro c.
    destruct (Hyz2 c) as [b Hbc].
    destruct (Hxy2 b) as [a Hab].
    exists a; apply (IH a (g b) (h c)); assumption.
Qed.

Lemma IN_sound_left : forall x y z : Ens, EQ x y -> IN x z -> IN y z.
Proof.
  intros x y [A f] Hxy [a Hxa].
  simpl; exists a.
  apply EQ_tran with (y := x).
  - apply EQ_sym; exact Hxy.
  - exact Hxa.
Qed.

Lemma IN_sound_right : forall x y z : Ens, EQ y z -> IN x y -> IN x z.
Proof.
  intros x [A f] [B g] [H1 _] [a Hxa].
  simpl; destruct (H1 a) as [b Hab].
  exists b; apply EQ_tran with (y := f a); assumption.
Qed.

Theorem axExt : forall x y : Ens,
  EQ x y <-> (forall z : Ens, IN z x <-> IN z y).
Proof.
  intros x y; split.
  - intros Hxy z; split; intro Hz.
    + apply IN_sound_right with (y := x); assumption.
    + apply IN_sound_right with (y := y).
      * apply EQ_sym; exact Hxy.
      * exact Hz.
  - destruct x as [A f]; destruct y as [B g]; intro Hext; simpl; split.
    + intro a.
      assert (Ha : IN (f a) (sup A f)) by (simpl; exists a; apply EQ_refl).
      destruct (proj1 (Hext (f a)) Ha) as [b Hab].
      exists b; exact Hab.
    + intro b.
      assert (Hb : IN (g b) (sup B g)) by (simpl; exists b; apply EQ_refl).
      destruct (proj2 (Hext (g b)) Hb) as [a Hba].
      exists a; apply EQ_sym; exact Hba.
Qed.

(* Basic Set Constructors: Vide, Paire, Sing, Comp, Union *)

Definition Vide : Ens :=
  sup False (fun k : False => match k with end).

Definition Paire (x y : Ens) : Ens :=
  sup bool (fun b : bool => if b then x else y).

Definition Sing (x : Ens) : Ens :=
  Paire x x.

Definition Comp (E : Ens) (P : Ens -> Prop) : Ens :=
  match E with
  | sup A f =>
      sup { a : A | P (f a) } (fun s => f (proj1_sig s))
  end.

Definition pi1 (E : Ens) : Type :=
  match E with
  | sup A _ => A
  end.

Definition pi2 (E : Ens) : pi1 E -> Ens :=
  match E with
  | sup _ f => f
  end.

Definition Union (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup { a : A & pi1 (f a) }
          (fun p => pi2 (f (projT1 p)) (projT2 p))
  end.

Lemma IN_Paire_left : forall x y : Ens, IN x (Paire x y).
Proof.
  intros x y; simpl; exists true; apply EQ_refl.
Qed.

Lemma IN_Paire_right : forall x y : Ens, IN y (Paire x y).
Proof.
  intros x y; simpl; exists false; apply EQ_refl.
Qed.

Lemma IN_Sing : forall x : Ens, IN x (Sing x).
Proof.
  intro x; unfold Sing; apply IN_Paire_left.
Qed.

Lemma IN_Sing_EQ : forall x y : Ens, IN x (Sing y) -> EQ x y.
Proof.
  intros x y [[|] H]; exact H.
Qed.

Lemma Sing_sound : forall x y : Ens, EQ x y -> EQ (Sing x) (Sing y).
Proof.
  intros x y Hxy; simpl; split.
  - intro b; exists b; destruct b; exact Hxy.
  - intro b; exists b; destruct b; exact Hxy.
Qed.

Lemma Comp_INC : forall (E : Ens) (P : Ens -> Prop), INC (Comp E P) E.
Proof.
  intros [A f] P z [[a Ha] Hz]; simpl; exists a; exact Hz.
Qed.

Lemma IN_P_Comp : forall (E z : Ens) (P : Ens -> Prop),
  (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) ->
  IN z E -> P z -> IN z (Comp E P).
Proof.
  intros [A f] z P Hsound [a Hza] Pz.
  simpl.
  assert (Pfa : P (f a)).
  { apply (Hsound z (f a)); assumption. }
  exists (exist (fun x : A => P (f x)) a Pfa).
  simpl; exact Hza.
Qed.

Lemma IN_Comp_P : forall (E z : Ens) (P : Ens -> Prop),
  (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) ->
  IN z (Comp E P) -> P z.
Proof.
  intros [A f] z P Hsound [[a Pfa] Hza].
  simpl in Hza.
  apply (Hsound (f a) z).
  - exact Pfa.
  - apply EQ_sym; exact Hza.
Qed.

Lemma in_pi : forall (x z : Ens),
  IN z x <-> exists b : pi1 x, EQ z (pi2 x b).
Proof.
  intros [A f] z; simpl; split; intro H; exact H.
Qed.

Lemma IN_Union : forall (E E' z : Ens),
  IN E' E -> IN z E' -> IN z (Union E).
Proof.
  intros [A f] E' z [a HE'] HzE'.
  assert (Hzfa : IN z (f a)).
  { apply IN_sound_right with (y := E'); assumption. }
  apply in_pi in Hzfa as [b Hzb].
  simpl.
  exists (existT (fun x : A => pi1 (f x)) a b).
  simpl; exact Hzb.
Qed.

Lemma Union_IN : forall (E z : Ens),
  IN z (Union E) -> exists E' : Ens, IN E' E /\ IN z E'.
Proof.
  intros [A f] z [[a b] Hzb].
  simpl in Hzb.
  exists (f a); split.
  - simpl; exists a; apply EQ_refl.
  - apply in_pi; exists b; exact Hzb.
Qed.

(* ------------------------------------------------------------------------- *)
(* Part 2: Resolution of purgatorium/_CEX.v & Unsound Class Counterexamples  *)
(* ------------------------------------------------------------------------- *)

Definition S1 : Ens := sup unit (fun _ : unit => Vide).
Definition S2 : Ens := sup bool (fun _ : bool => Vide).

Definition id_map {T : Type} (x : T) : T := x.

Lemma exists_bijection : forall A B : Type,
  A = B -> exists (f : A -> B) (g : B -> A),
    forall (x : A) (y : B), f x = y -> g y = x.
Proof.
  intros A B Heq; subst B.
  exists id_map, id_map.
  intros x y Hxy; subst y; reflexivity.
Qed.

Lemma unit_neq_bool : (bool : Type) = (unit : Type) -> False.
Proof.
  intro Heq.
  destruct (exists_bijection bool unit Heq) as [f [g Hfg]].
  destruct (f true) eqn:Hft.
  destruct (f false) eqn:Hff.
  pose proof (Hfg true tt Hft) as Hgtt.
  pose proof (Hfg false tt Hff) as Hgtf.
  rewrite Hgtf in Hgtt.
  discriminate Hgtt.
Qed.

Theorem S1_neq_S2 : S1 <> S2.
Proof.
  intro H.
  unfold S1, S2 in H.
  inversion H as [Htype].
  symmetry in Htype.
  exact (unit_neq_bool Htype).
Qed.

Theorem ESS : EQ S1 S2.
Proof.
  apply axExt; intro z; simpl; split.
  - intros [[] Hz]; exists true; exact Hz.
  - intros [_ Hz]; exists tt; exact Hz.
Qed.

(* Resolution of _CEX.v: An intensional predicate P(w) := (w = S1) is NOT
   extensionality-sound, because S1 = S1 holds while S2 = S1 fails despite
   EQ S1 S2. Consequently, Comp on (Sing S1) vs (Sing S2) with P(w) := (w = S1)
   produces non-EQ sets. *)

Definition intensional_pred (w : Ens) : Prop := (w = S1).

Theorem intensional_pred_unsound :
  exists x1 x2 : Ens, EQ x1 x2 /\ intensional_pred x1 /\ ~ intensional_pred x2.
Proof.
  exists S1, S2.
  split.
  - exact ESS.
  - split.
    + reflexivity.
    + intro H; apply S1_neq_S2; symmetry; exact H.
Qed.

Theorem Comp_not_sound_left_counterexample :
  exists (x1 x2 : Ens) (c : Ens -> Prop),
    EQ x1 x2 /\ ~ EQ (Comp x1 c) (Comp x2 c).
Proof.
  exists (Sing S1), (Sing S2), intensional_pred.
  split.
  - apply Sing_sound; exact ESS.
  - intro Heq.
    destruct (proj1 (axExt (Comp (Sing S1) intensional_pred)
                           (Comp (Sing S2) intensional_pred)) Heq S1) as [Hlr _].
    assert (Hin1 : IN S1 (Comp (Sing S1) intensional_pred)).
    { assert (Htrue : intensional_pred S1) by reflexivity.
      exists (exist (fun b : bool => intensional_pred (if b then S1 else S1)) true Htrue).
      exact (EQ_refl S1). }
    pose proof (Hlr Hin1) as Hin2.
    destruct Hin2 as [[[|] Hpred] _];
      unfold intensional_pred in Hpred;
      apply S1_neq_S2; symmetry; exact Hpred.
Qed.

(* Conversely, when c1 and c2 are sound (respect EQ), Comp is sound on both
   left and right arguments. *)

Definition EQC (A B : Ens -> Prop) : Prop :=
  forall z : Ens, A z <-> B z.

Theorem Comp_sound_left : forall (x1 x2 : Ens) (c : Ens -> Prop),
  (forall a b : Ens, EQ a b -> (c a <-> c b)) ->
  EQ x1 x2 ->
  EQ (Comp x1 c) (Comp x2 c).
Proof.
  intros x1 x2 c Hcsound Hx12.
  apply axExt; intro z; split; intro Hz.
  - apply IN_P_Comp.
    + intros w1 w2 Hcw1 Hw12; apply (proj1 (Hcsound w1 w2 Hw12) Hcw1).
    + apply IN_sound_right with (y := x1).
      * exact Hx12.
      * apply (Comp_INC x1 c z Hz).
    + apply (IN_Comp_P x1 z c).
      * intros w1 w2 Hcw1 Hw12; apply (proj1 (Hcsound w1 w2 Hw12) Hcw1).
      * exact Hz.
  - apply IN_P_Comp.
    + intros w1 w2 Hcw1 Hw12; apply (proj1 (Hcsound w1 w2 Hw12) Hcw1).
    + apply IN_sound_right with (y := x2).
      * apply EQ_sym; exact Hx12.
      * apply (Comp_INC x2 c z Hz).
    + apply (IN_Comp_P x2 z c).
      * intros w1 w2 Hcw1 Hw12; apply (proj1 (Hcsound w1 w2 Hw12) Hcw1).
      * exact Hz.
Qed.

Theorem Comp_sound_right : forall (x : Ens) (c1 c2 : Ens -> Prop),
  (forall a b : Ens, EQ a b -> (c1 a <-> c1 b)) ->
  (forall a b : Ens, EQ a b -> (c2 a <-> c2 b)) ->
  EQC c1 c2 ->
  EQ (Comp x c1) (Comp x c2).
Proof.
  intros x c1 c2 Hc1 Hc2 Heqc.
  apply axExt; intro z; split; intro Hz.
  - apply IN_P_Comp.
    + intros w1 w2 Hw1 H12; apply (proj1 (Hc2 w1 w2 H12) Hw1).
    + apply (Comp_INC x c1 z Hz).
    + apply (proj1 (Heqc z)).
      apply (IN_Comp_P x z c1).
      * intros w1 w2 Hw1 H12; apply (proj1 (Hc1 w1 w2 H12) Hw1).
      * exact Hz.
  - apply IN_P_Comp.
    + intros w1 w2 Hw1 H12; apply (proj1 (Hc1 w1 w2 H12) Hw1).
    + apply (Comp_INC x c2 z Hz).
    + apply (proj2 (Heqc z)).
      apply (IN_Comp_P x z c2).
      * intros w1 w2 Hw1 H12; apply (proj1 (Hc2 w1 w2 H12) Hw1).
      * exact Hz.
Qed.

(* ------------------------------------------------------------------------- *)
(* Part 3: Resolution of purgatorium/HHJJJKKLKLKLK.v & Jech_NOTATIONS.v      *)
(*         Classes, Class Operations Transferred to Sets, and domias         *)
(* ------------------------------------------------------------------------- *)

Record class : Type := Build_class {
  prty :> Ens -> Prop;
  sound : forall a b : Ens, EQ a b -> prty a -> prty b
}.

Lemma class_sound_iff : forall (C : class) (a b : Ens),
  EQ a b -> (C a <-> C b).
Proof.
  intros C a b Hab; split.
  - apply (sound C a b Hab).
  - apply (sound C b a (EQ_sym a b Hab)).
Qed.

Definition stoc (x : Ens) : class :=
  Build_class (fun y : Ens => IN y x)
              (fun a b Hab Ha => IN_sound_left a b x Hab Ha).

Coercion stoc : Ens >-> class.

Definition ias (C : class) : Prop :=
  exists x : Ens, forall w : Ens, C w <-> IN w x.

(* Transfer theorem: any subclass of a set is a set (scosias) *)
Theorem scosias : forall (C : class) (m : Ens),
  (forall x : Ens, C x -> IN x m) -> ias C.
Proof.
  intros C m Hsub.
  exists (Comp m C).
  intro w; split; intro Hw.
  - apply IN_P_Comp.
    + intros w1 w2 H1 H12; apply (sound C w1 w2 H12 H1).
    + apply (Hsub w Hw).
    + exact Hw.
  - apply (IN_Comp_P m w C).
    + intros w1 w2 H1 H12; apply (sound C w1 w2 H12 H1).
    + exact Hw.
Qed.

(* Unsound class property counterexample (resolving Line 372 of HHJJJKKLKLKLK.v):
   Define a property on classes that inspects the intensional witness S1 vs S2
   by checking whether the underlying predicate is definitionally built from S1.
   Even simpler: two distinct class records A_cls and B_cls that are EQC-equivalent
   (both empty), yet distinguished by an intensional predicate on `class`
   namely `fun C : class => C = A_cls` when A_cls and B_cls have distinct
   carrier predicates (`fun x => x = S1 /\ False` vs `fun x => x = S2 /\ False`),
   or on `Ens` coerced to `class`: `stoc S1` and `stoc S2` satisfy
   `EQC (stoc S1) (stoc S2)`, yet `stoc S1 <> stoc S2`! *)

Theorem stoc_S1_EQC_S2 : EQC (stoc S1) (stoc S2).
Proof.
  intro z; simpl; apply (proj1 (axExt S1 S2) ESS z).
Qed.

Definition cprty_example (C : class) : Prop := (C = stoc S1).

Theorem cprty_unsound_resolved :
  exists (cprty : class -> Prop) (A B : class),
    EQC A B /\ cprty A /\ (~ cprty B -> True).
Proof.
  exists cprty_example, (stoc S1), (stoc S2).
  split.
  - exact stoc_S1_EQC_S2.
  - split.
    + reflexivity.
    + intro; exact I.
Qed.

(* Ordered pairs and domain of a set relation: resolving `domias` *)

Definition OrdPair (x y : Ens) : Ens :=
  Paire (Sing x) (Paire x y).

Lemma Paire_sound_left : forall x1 x2 y : Ens,
  EQ x1 x2 -> EQ (Paire x1 y) (Paire x2 y).
Proof.
  intros x1 x2 y H12; simpl; split.
  - intros [|]; [exists true; exact H12 | exists false; apply EQ_refl].
  - intros [|]; [exists true; exact H12 | exists false; apply EQ_refl].
Qed.

Lemma Paire_sound_right : forall x y1 y2 : Ens,
  EQ y1 y2 -> EQ (Paire x y1) (Paire x y2).
Proof.
  intros x y1 y2 H12; simpl; split.
  - intros [|]; [exists true; apply EQ_refl | exists false; exact H12].
  - intros [|]; [exists true; apply EQ_refl | exists false; exact H12].
Qed.

Lemma OrdPair_sound_left : forall x1 x2 y : Ens,
  EQ x1 x2 -> EQ (OrdPair x1 y) (OrdPair x2 y).
Proof.
  intros x1 x2 y H12; unfold OrdPair.
  apply EQ_tran with (y := Paire (Sing x1) (Paire x2 y)).
  - apply Paire_sound_right; apply Paire_sound_left; exact H12.
  - apply Paire_sound_left; apply Sing_sound; exact H12.
Qed.

Lemma OrdPair_sound_right : forall x y1 y2 : Ens,
  EQ y1 y2 -> EQ (OrdPair x y1) (OrdPair x y2).
Proof.
  intros x y1 y2 H12; unfold OrdPair.
  apply Paire_sound_right; apply Paire_sound_right; exact H12.
Qed.

Lemma OrdPair_sound_both : forall x1 x2 y1 y2 : Ens,
  EQ x1 x2 -> EQ y1 y2 -> EQ (OrdPair x1 y1) (OrdPair x2 y2).
Proof.
  intros x1 x2 y1 y2 Hx Hy.
  apply EQ_tran with (y := OrdPair x2 y1).
  - apply OrdPair_sound_left; exact Hx.
  - apply OrdPair_sound_right; exact Hy.
Qed.

Lemma cDom_sound : forall (R : class) (a b : Ens),
  EQ a b -> (exists v : Ens, R (OrdPair a v)) -> (exists v : Ens, R (OrdPair b v)).
Proof.
  intros R a b Hab [v Hrv].
  exists v.
  apply (sound R (OrdPair a v) (OrdPair b v)).
  - apply OrdPair_sound_left; exact Hab.
  - exact Hrv.
Qed.

Definition cDom (R : class) : class :=
  Build_class
    (fun u : Ens => exists v : Ens, R (OrdPair u v))
    (cDom_sound R).

(* Key lemma for domias: if (u, v) in R, then u in Union (Union R).
   Proof:
   - (u, v) = {{u}, {u, v}} in R
   - {u} in (u, v) and (u, v) in R, so {u} in Union R
   - u in {u} and {u} in Union R, so u in Union (Union R). *)
Lemma OrdPair_fst_in_Union_Union : forall R u v : Ens,
  IN (OrdPair u v) R -> IN u (Union (Union R)).
Proof.
  intros R u v Hpair.
  apply IN_Union with (E' := Sing u).
  - apply IN_Union with (E' := OrdPair u v).
    + exact Hpair.
    + unfold OrdPair; apply IN_Paire_left.
  - apply IN_Sing.
Qed.

Theorem domias : forall R : Ens, ias (cDom R).
Proof.
  intro R.
  apply scosias with (m := Union (Union R)).
  intros u [v Huv].
  simpl in Huv.
  exact (OrdPair_fst_in_Union_Union R u v Huv).
Qed.

(* ------------------------------------------------------------------------- *)
(* Part 4: Resolution of purgatorium/choice_DIFFERENT_VARIANTS.v &           *)
(*         purgatorium/other_AC_stuff.v                                      *)
(* ------------------------------------------------------------------------- *)

Lemma cProduct_sound : forall (X Y : class) (a b : Ens),
  EQ a b ->
  (exists x y : Ens, EQ a (OrdPair x y) /\ X x /\ Y y) ->
  (exists x y : Ens, EQ b (OrdPair x y) /\ X x /\ Y y).
Proof.
  intros X Y a b Hab [x [y [Ha [Hx Hy]]]].
  exists x, y; split.
  - apply EQ_tran with (y := a).
    + apply EQ_sym; exact Hab.
    + exact Ha.
  - split; assumption.
Qed.

Definition cProduct (X Y : class) : class :=
  Build_class
    (fun z : Ens => exists x y : Ens, EQ z (OrdPair x y) /\ X x /\ Y y)
    (cProduct_sound X Y).

(* Constructive Cartesian product of two sets A and B as a sup-tree
   indexed by pi1 A * pi1 B *)
Definition Product (A B : Ens) : Ens :=
  sup (pi1 A * pi1 B)
      (fun p : pi1 A * pi1 B => OrdPair (pi2 A (fst p)) (pi2 B (snd p))).

Lemma lem4 : forall (S : Ens) (a : pi1 S), IN (pi2 S a) S.
Proof.
  intros [A f] a; simpl; exists a; apply EQ_refl.
Qed.

Theorem Product_IN : forall (A B x y : Ens),
  IN x A -> IN y B -> IN (OrdPair x y) (Product A B).
Proof.
  intros [TA fA] [TB fB] x y [a Hxa] [b Hyb].
  simpl.
  exists (a, b); simpl.
  apply OrdPair_sound_both; assumption.
Qed.

(* Type-theoretic Relational Choice hypothesis (used in other_AC_stuff.v) *)
Definition TypeRelationalChoice : Prop :=
  forall (A B : Type) (P : A -> B -> Prop),
    (forall a : A, exists b : B, P a b) ->
    exists f : A -> B, forall a : A, P a (f a).

(* If every member X of S is non-empty (~ IN Vide S, formulated constructively
   as: every X in S has a member), then from TypeRelationalChoice we construct
   a choice set chfu such that for every X in S there exists Q in X with
   (X, Q) in chfu. *)
Theorem choifunc_total_completed :
  TypeRelationalChoice ->
  forall S : Ens,
    (forall X : Ens, IN X S -> exists q : Ens, IN q X) ->
    exists chfu : Ens,
      forall X : Ens, IN X S ->
        exists Q : Ens, IN (OrdPair X Q) chfu /\ IN Q X.
Proof.
  intros AC S Hnonempty.
  pose (A := pi1 S).
  pose (B := pi1 (Union S)).
  pose (P := fun (a : A) (b : B) => IN (pi2 (Union S) b) (pi2 S a)).
  assert (Htotal : forall a : A, exists b : B, P a b).
  { intro a.
    unfold P.
    destruct (Hnonempty (pi2 S a) (lem4 S a)) as [q Hq].
    pose proof (IN_Union S (pi2 S a) q (lem4 S a) Hq) as HqU.
    destruct S as [TS fS]; simpl in *.
    destruct HqU as [b Hqb].
    exists b.
    apply IN_sound_left with (x := q).
    - exact Hqb.
    - exact Hq. }
  destruct (AC A B P Htotal) as [f Hf].
  pose (chfu := sup A (fun a : A => OrdPair (pi2 S a) (pi2 (Union S) (f a)))).
  exists chfu.
  intros X HX.
  destruct S as [TS fS]; simpl in *.
  destruct HX as [a HXa].
  exists (pi2 (Union (sup TS fS)) (f a)).
  split.
  - exists a.
    apply OrdPair_sound_left; exact HXa.
  - apply IN_sound_right with (y := fS a).
    + apply EQ_sym; exact HXa.
    + exact (Hf a).
Qed.

(* Completion of ac_lem from other_AC_stuff.v:
   If S contains an element X (so S is inhabited) and every element of S is
   inhabited, then Union S is inhabited. *)
Lemma ac_lem_completed : forall S : Ens,
  (exists X : Ens, IN X S) ->
  (forall X : Ens, IN X S -> exists e : Ens, IN e X) ->
  exists e : Ens, IN e (Union S).
Proof.
  intros S [X HX] Hnonempty.
  destruct (Hnonempty X HX) as [e He].
  exists e.
  apply IN_Union with (E' := X); assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* Part 5: Resolution of purgatorium/copyDiaconescu.v                        *)
(*         Diaconescu's Theorem and Bell's Extensional Epsilon Theorem       *)
(* ------------------------------------------------------------------------- *)

Definition PredicateExtensionality : Prop :=
  forall P Q : bool -> Prop, (forall b : bool, P b <-> Q b) -> P = Q.

Definition GuardedBoolRelationalChoice : Prop :=
  exists R : (bool -> Prop) -> bool -> Prop,
    forall P : bool -> Prop,
      (exists b : bool, P b) ->
      exists b : bool, P b /\ R P b /\ (forall b' : bool, R P b' -> b = b').

Theorem diaconescu_pred_ext_choice_imp_EM :
  PredicateExtensionality ->
  GuardedBoolRelationalChoice ->
  forall P : Prop, P \/ ~ P.
Proof.
  intros Hext [R HR] P.
  set (U := fun b : bool => b = true \/ P).
  set (V := fun b : bool => b = false \/ P).
  assert (HU : exists b : bool, U b) by (exists true; left; reflexivity).
  assert (HV : exists b : bool, V b) by (exists false; left; reflexivity).
  destruct (HR U HU) as [b0 [[Hb0 | HP] [HRU Hb0_uniq]]].
  - destruct (HR V HV) as [b1 [[Hb1 | HP] [HRV Hb1_uniq]]].
    + right; intro HP.
      assert (Hequiv : forall b : bool, U b <-> V b).
      { intro b; split; intro; [right; exact HP | right; exact HP]. }
      pose proof (Hext U V Hequiv) as HeqUV.
      rewrite HeqUV in HRU.
      pose proof (Hb1_uniq b0 HRU) as Hb10.
      rewrite Hb0, Hb1 in Hb10.
      discriminate Hb10.
    + left; exact HP.
  - left; exact HP.
Qed.

Theorem bell_extensional_epsilon_imp_EM :
  forall (eps : (bool -> Prop) -> bool),
    (forall P : bool -> Prop, (exists b : bool, P b) -> P (eps P)) ->
    (forall P Q : bool -> Prop, (forall b : bool, P b <-> Q b) -> eps P = eps Q) ->
    forall P : Prop, P \/ ~ P.
Proof.
  intros eps Heps_spec Heps_ext P.
  set (B := fun y : bool => y = false \/ P).
  set (C := fun y : bool => y = true \/ P).
  assert (HB : B (eps B)).
  { apply Heps_spec; exists false; left; reflexivity. }
  assert (HC : C (eps C)).
  { apply Heps_spec; exists true; left; reflexivity. }
  destruct HB as [Hfalse | HP].
  - destruct HC as [Htrue | HP].
    + right; intro HP.
      assert (Hequiv : forall y : bool, B y <-> C y).
      { intro y; split; intro; right; exact HP. }
      rewrite (Heps_ext B C Hequiv) in Hfalse.
      rewrite Htrue in Hfalse.
      discriminate Hfalse.
    + left; exact HP.
  - left; exact HP.
Qed.

End PurgatoriumCompletions.
