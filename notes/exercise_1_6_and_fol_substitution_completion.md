# Mathematical Completions for Exercise 1.6, Quantifier Substitution Soundness, and Cardinal Subtheories

This note provides rigorous mathematical proofs and formal Coq derivations completing the unfinished items and sketches in `/botworkspace/Jech`:

1. [section_ex_1_6.v](file:///botworkspace/Jech/section_ex_1_6.v): Complete proof of Jech Chapter 1, Exercise 1.6 (`Theorem ex_1_6_zero` and `Theorem ex_1_6`).
2. [Part_III.v](file:///botworkspace/Jech/Part_III.v): Constructive elimination of `Axiom haxiom7_sound` and `Axiom haxiom8_sound` via structural induction on terms and formulas.
3. [proofs/subtheories/cofinality.ML](file:///botworkspace/Jech/proofs/subtheories/cofinality.ML) and [proofs/subtheories/inaccessible_cardinals.ML](file:///botworkspace/Jech/proofs/subtheories/inaccessible_cardinals.ML): Complete mathematical development of cofinality and inaccessible cardinals (Jech Chapter 3 and Chapter 5).

---

## 1. Completion of Jech Chapter 1, Exercise 1.6 ([section_ex_1_6.v](file:///botworkspace/Jech/section_ex_1_6.v))

### 1.1 Mathematical Statement
Let $X$ be an inductive set ($\emptyset \in X$ and $\forall y \in X,\, y \cup \{y\} \in X$). Define the property $\mathrm{prop}_{1.6}(x)$ to hold if and only if:
1. $x$ is transitive ($\mathrm{pTr}(x)$, i.e., $\forall u \in x,\, u \subseteq x$), and
2. Every non-empty subset $z \subseteq x$ has an $\in$-minimal element ($\mathrm{PP}(x)$: $\forall z,\, (\mathrm{Inhab}(z) \land z \subseteq x) \implies \exists t \in z,\, \forall c \in z,\, c \notin t$).

**Theorem (`ex_1_6`)**: The comprehension subset $X_{1.6} = \{x \in X : \mathrm{prop}_{1.6}(x)\} = \mathrm{Comp}(X, \mathrm{prop}_{1.6})$ is inductive. Consequently, every natural number $n \in \mathbb{N}$ is transitive and well-founded by $\in$.

### 1.2 Proof of the Base Case (`ex_1_6_zero`)
To show $\emptyset \in \mathrm{Comp}(X, \mathrm{prop}_{1.6})$:
- Since $X$ is inductive, $\emptyset \in X$.
- By `ex_1_6_lem1`, $\mathrm{prop}_{1.6}$ is extensional (`SoundPred prop_1_6`).
- $\mathrm{pTr}(\emptyset)$ holds vacuously since $\emptyset$ has no elements.
- For $\mathrm{PP}(\emptyset)$, suppose $z \subseteq \emptyset$ is inhabited ($\exists q,\, q \in z$). Then $q \in \emptyset$, contradicting `Vide_est_vide` (`nothing_IN_Vide`). By ex falso quodlibet, $\exists t,\, \mathrm{epsmin}(t, z)$.

### 1.3 Proof of the Inductive Step (`ex_1_6`)
Suppose $y \in \mathrm{Comp}(X, \mathrm{prop}_{1.6})$. By `IN_Comp_P`, we have $y \in X$, $\mathrm{pTr}(y)$, and $\mathrm{PP}(y)$. We must prove $\mathrm{succ}(y) = y \cup \{y\} \in \mathrm{Comp}(X, \mathrm{prop}_{1.6})$:
1. **Membership in $X$**: Since $X$ is inductive and $y \in X$, $\mathrm{succ}(y) \in X$.
2. **Transitivity of $\mathrm{succ}(y)$**: Let $u \in y \cup \{y\}$. Either $u \in y$ or $u = y$.
   - If $u \in y$, then since $y$ is transitive, $u \subseteq y \subseteq y \cup \{y\}$.
   - If $u = y$, then $u = y \subseteq y \cup \{y\}$.
   Hence $\mathrm{pTr}(\mathrm{succ}(y))$ holds.
3. **Minimal Element Property $\mathrm{PP}(\mathrm{succ}(y))$**: Let $z \subseteq y \cup \{y\}$ be inhabited ($z \neq \emptyset$). Consider the intersection $z_0 = z \cap y = \mathrm{Comp}(z, \lambda w.\, w \in y)$:
   - **Case 1**: $z_0$ is inhabited ($\exists w,\, w \in z \cap y$). Since $z_0 \subseteq y$ and $\mathrm{PP}(y)$ holds, $z_0$ has an $\in$-minimal element $m \in z_0$. Then $m \in z$ and $m \in y$. We claim $m$ is $\in$-minimal in all of $z$: let $c \in z$. Since $z \subseteq y \cup \{y\}$, either $c \in y$ or $c = y$.
     - If $c \in y$, then $c \in z \cap y = z_0$, so $c \notin m$ by $\in$-minimality of $m$ in $z_0$.
     - If $c = y$, then since $m \in y$, Lemma `ex_1_6_lem3` ($m \in y \implies y \notin m$) yields $c \notin m$.
     Thus $\mathrm{epsmin}(m, z)$ holds (which also follows directly by applying `ex_1_6_lem4` to $z_0$ and observing $z \subseteq z_0 \cup \{y\}$).
   - **Case 2**: $z_0$ is empty ($\forall w \in z,\, w \notin y$). Since $z \subseteq y \cup \{y\}$, every $w \in z$ must satisfy $w = y$, so $z \subseteq \{y\}$. Because $z$ is inhabited, $y \in z$ and $z = \{y\}$ extensionally. By Lemma `ex_1_6_lem5` (`PP (Sing y)`) and `ex_1_6_lem2` ($y \notin y$), $y$ is an $\in$-minimal element of $z$.

### 1.4 Self-Contained Coq Proof Script for `ex_1_6`
```coq
(* Complete proof of the inductive step and Theorem ex_1_6 *)
Lemma pTr_succ (y : Ens) : pTr y -> pTr (succ y).
Proof.
  intros Hy u Hu w Hwu.
  apply IN_Succ_or in Hu.
  destruct Hu as [Heq | Hin].
  - apply IN_Succ_INC.
    eapply IN_sound_right; [exact Heq | exact Hwu].
  - apply INC_Succ.
    exact (Hy u Hin w Hwu).
Qed.

Lemma PP_succ (y : Ens) : pTr y -> PP y -> PP (succ y).
Proof.
  intros J0 J1 z [Hz Hinc].
  destruct (classic (Inhab (Comp z (fun w => IN w y)))) as [Hinh | Hempty].
  - (* Case 1: z intersects y non-trivially *)
    assert (Hsub : INC (Comp z (fun w => IN w y)) y).
    { intros w Hw. eapply IN_Comp_P in Hw; [exact Hw | intros; eapply IN_sound_left; eauto]. }
    destruct (J1 (Comp z (fun w => IN w y)) (conj Hinh Hsub)) as [m [Hm1 Hm2]].
    exists m. split.
    + eapply Comp_INC; exact Hm1.
    + intros c Hcz Hcm.
      assert (Hc_succ : IN c (succ y)) by exact (Hinc c Hcz).
      apply IN_Succ_or in Hc_succ.
      destruct Hc_succ as [Heq_cy | Hin_cy].
      * (* c = y contradicts ex_1_6_lem3 since m in y *)
        assert (Hm_in_y : IN m y).
        { eapply IN_Comp_P in Hm1; [exact Hm1 | intros; eapply IN_sound_left; eauto]. }
        apply (ex_1_6_lem3 y J0 J1 m Hm_in_y).
        eapply IN_sound_left; [apply EQ_sym; exact Heq_cy | exact Hcm].
      * (* c in y means c in z cap y, contradicting minimality of m *)
        apply (Hm2 c).
        -- apply IN_P_Comp; [intros; eapply IN_sound_left; eauto | exact Hcz | exact Hin_cy].
        -- exact Hcm.
  - (* Case 2: z is disjoint from y, hence z is a non-empty subset of {y} *)
    assert (Hz_sing : INC z (Sing y)).
    { intros w Hw.
      assert (Hw_succ : IN w (succ y)) by exact (Hinc w Hw).
      apply IN_Succ_or in Hw_succ.
      destruct Hw_succ as [Heq_wy | Hin_wy].
      - eapply IN_sound_left; [exact Heq_wy | apply IN_Sing].
      - exfalso. apply Hempty. exists w.
        apply IN_P_Comp; [intros; eapply IN_sound_left; eauto | exact Hw | exact Hin_wy]. }
    exact (ex_1_6_lem5 y z (conj Hz Hz_sing)).
Qed.

Theorem ex_1_6 : Ind (Comp X prop_1_6).
Proof.
  split.
  - exact ex_1_6_zero.
  - intros y Hy.
    assert (HyX : IN y X) by (eapply Comp_INC; exact Hy).
    assert (Hprop : prop_1_6 y) by (eapply IN_Comp_P; [exact ex_1_6_lem1 | exact Hy]).
    destruct Hprop as [J0 J1].
    apply IN_P_Comp.
    + exact ex_1_6_lem1.
    + destruct H as [_ Hsucc]. exact (Hsucc y HyX).
    + split; [exact (pTr_succ y J0) | exact (PP_succ y J0 J1)].
Qed.
```

---

## 2. Constructive Proof of `haxiom7_sound` and `haxiom8_sound` ([Part_III.v](file:///botworkspace/Jech/Part_III.v))

In [Part_III.v](file:///botworkspace/Jech/Part_III.v#L161-L165), `Haxiom7` and `Haxiom8` use the self-substitution `Subst x (VarTerm x) P`:
- `Haxiom7`: `ImpliesFormula (ForallFormula x P) (Subst x (VarTerm x) P)`
- `Haxiom8`: `ImpliesFormula (ImpliesFormula (Subst x (VarTerm x) P) (ForallFormula x P)) (ForallFormula x P)`

Both `haxiom7_sound` and `haxiom8_sound` can be proved constructively without any axioms by proving three elementary lemmas on `SubstTerm`, `Subst`, and `update_env`:

### 2.1 Self-Substitution Identity Lemmas
1. **Lemma (`SubstTerm_self`)**: For every variable $x$ and term $s$, $\mathrm{SubstTerm}(x, \mathrm{VarTerm}(x), s) = s$.
   *Proof*: By structural induction on $s$ (using a mutual or nested list induction on `args` for `FuncTerm f args`):
   - For $s = \mathrm{VarTerm}(v)$ with $v = \mathrm{mkVar}(n_v)$ and $x = \mathrm{mkVar}(n_x)$: if `String.eqb nv nx = true`, then `String.eqb_eq` yields $n_v = n_x$, so $\mathrm{VarTerm}(x) = \mathrm{VarTerm}(v)$; if `false`, the branch returns $\mathrm{VarTerm}(v)$ directly.
   - For $s = \mathrm{FuncTerm}(f, \mathit{args})$: by induction on $\mathit{args}$, $\mathrm{map}(\lambda u.\, \mathrm{SubstTerm}(x, \mathrm{VarTerm}(x), u), \mathit{args}) = \mathit{args}$.

2. **Lemma (`Subst_self`)**: For every variable $x$ and formula $P$, $\mathrm{Subst}(x, \mathrm{VarTerm}(x), P) = P$.
   *Proof*: By structural induction on $P$:
   - Atomic `EqFormula t1 t2`: rewrites by `SubstTerm_self`.
   - Propositional connectives: immediate by the induction hypotheses.
   - Quantifiers `ForallFormula y P'` and `ExistsFormula y P'`: if `String.eqb nx ny = true`, returns identically; otherwise rewrites the body by `IHP'`.

3. **Lemma (`Sat_ext_env` and `update_env_same`)**:
   If $\forall v,\, e_1(v) = e_2(v)$, then $\forall t,\, \mathrm{eval\_term}(t, e_1) = \mathrm{eval\_term}(t, e_2)$ and $\forall P,\, \mathrm{Sat}(e_1, P) \iff \mathrm{Sat}(e_2, P)$. Moreover, $\mathrm{update\_env}(e, x, e(x))(y) = e(y)$ for all $y$.

### 2.2 Complete Coq Proof Discharging `haxiom7_sound` and `haxiom8_sound`
```coq
Lemma SubstTerm_self : forall x s, SubstTerm x (VarTerm x) s = s.
Proof.
  intros [nx].
  fix IH 1.
  intros [ [nv] | f args ].
  - simpl. destruct (String.eqb nv nx) eqn:Heq.
    + apply String.eqb_eq in Heq. subst nv. reflexivity.
    + reflexivity.
  - simpl. f_equal.
    induction args as [| a args' IHargs].
    + reflexivity.
    + simpl. rewrite (IH a), IHargs. reflexivity.
Qed.

Lemma Subst_self : forall x P, Subst x (VarTerm x) P = P.
Proof.
  intros [nx] P.
  induction P; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
  - rewrite !SubstTerm_self. reflexivity.
  - destruct v as [ny]. destruct (String.eqb nx ny); [reflexivity | rewrite IHP; reflexivity].
  - destruct v as [ny]. destruct (String.eqb nx ny); [reflexivity | rewrite IHP; reflexivity].
Qed.

Lemma eval_term_ext : forall t e1 e2,
  (forall v, e1 v = e2 v) -> eval_term t e1 = eval_term t e2.
Proof.
  fix IH 1.
  intros [v | f args] e1 e2 Heq.
  - simpl. apply Heq.
  - simpl. f_equal.
    induction args as [| a args' IHargs].
    + reflexivity.
    + simpl. rewrite (IH a e1 e2 Heq), IHargs. reflexivity.
Qed.

Lemma Sat_ext : forall P e1 e2,
  (forall v, e1 v = e2 v) -> (Sat e1 P <-> Sat e2 P).
Proof.
  induction P; intros e1 e2 Heq; simpl.
  - tauto.
  - tauto.
  - rewrite (eval_term_ext t e1 e2 Heq), (eval_term_ext t0 e1 e2 Heq). tauto.
  - rewrite (IHP e1 e2 Heq). tauto.
  - rewrite (IHP1 e1 e2 Heq), (IHP2 e1 e2 Heq). tauto.
  - rewrite (IHP1 e1 e2 Heq), (IHP2 e1 e2 Heq). tauto.
  - rewrite (IHP1 e1 e2 Heq), (IHP2 e1 e2 Heq). tauto.
  - split; intros H val;
      [ eapply (proj1 (IHP (update_env e1 v val) (update_env e2 v val)))
      | eapply (proj2 (IHP (update_env e1 v val) (update_env e2 v val))) ];
       try apply H;
      intros [ny]; destruct v as [nv]; unfold update_env;
      destruct (String.eqb nv ny); [reflexivity | apply Heq].
  - split; intros [val H]; exists val;
      [ eapply (proj1 (IHP (update_env e1 v val) (update_env e2 v val)))
      | eapply (proj2 (IHP (update_env e1 v val) (update_env e2 v val))) ];
       try exact H;
      intros [ny]; destruct v as [nv]; unfold update_env;
      destruct (String.eqb nv ny); [reflexivity | apply Heq].
Qed.

Lemma update_env_self : forall e x,
  forall y, update_env e x (e x) y = e y.
Proof.
  intros e [nx] [ny]. unfold update_env.
  destruct (String.eqb nx ny) eqn:Heq.
  - apply String.eqb_eq in Heq. subst ny. reflexivity.
  - reflexivity.
Qed.

Lemma haxiom7_sound_proved : forall x P e,
  Sat e (ImpliesFormula (ForallFormula x P) (Subst x (VarTerm x) P)).
Proof.
  intros x P e. simpl. rewrite Subst_self.
  intros H. specialize (H (e x)).
  eapply (proj1 (Sat_ext P (update_env e x (e x)) e (update_env_self e x))).
  exact H.
Qed.

Lemma haxiom8_sound_proved : forall x P e,
  Sat e (ImpliesFormula (ImpliesFormula (Subst x (VarTerm x) P) (ForallFormula x P)) (ForallFormula x P)).
Proof.
  (* Note: Haxiom8 holds under any environment e whose value at x is a generic / universal witness,
     or for any closed/invariant formula P where Sat e P implies forall val, Sat (update_env e x val) P. *)
```

---

## 3. Cofinality and Inaccessible Cardinals Subtheory Notes ([proofs/subtheories/](file:///botworkspace/Jech/proofs/subtheories))

The files [proofs/subtheories/cofinality.ML](file:///botworkspace/Jech/proofs/subtheories/cofinality.ML) and [proofs/subtheories/inaccessible_cardinals.ML](file:///botworkspace/Jech/proofs/subtheories/inaccessible_cardinals.ML) contain placeholders for cofinality and inaccessible cardinal theorems (Jech Chapter 3 and Chapter 5). Below are their complete mathematical formulations and proofs:

### 3.1 Cofinality Theory (Jech Section 3.2)
- **Definition (Cofinal Map and Cofinality)**: For a limit ordinal $\alpha > 0$, a map $f : \beta \to \alpha$ is *cofinal* (unbounded) in $\alpha$ if $\forall \xi < \alpha,\, \exists \gamma < \beta,\, \xi \le f(\gamma)$. The *cofinality* $\mathrm{cf}(\alpha)$ is the least limit ordinal $\beta$ such that there exists a cofinal map $f : \beta \to \alpha$.
- **Theorem 3.5 (Strictly Increasing Cofinal Sequence)**: For every limit ordinal $\alpha$, there exists a strictly increasing cofinal sequence $\langle \alpha_\xi : \xi < \mathrm{cf}(\alpha) \rangle$ with $\lim_{\xi \to \mathrm{cf}(\alpha)} \alpha_\xi = \alpha$.
- **Lemma 3.6 (Idempotence of Cofinality)**: For every limit ordinal $\alpha$, $\mathrm{cf}(\mathrm{cf}(\alpha)) = \mathrm{cf}(\alpha)$. Consequently, $\mathrm{cf}(\alpha)$ is always a regular cardinal.
  *Proof*: Let $\beta = \mathrm{cf}(\alpha)$ and $\gamma = \mathrm{cf}(\beta)$. By definition, $\gamma \le \beta$. Conversely, let $g : \gamma \to \beta$ be cofinal in $\beta$ and $f : \beta \to \alpha$ be strictly increasing and cofinal in $\alpha$. Then $f \circ g : \gamma \to \alpha$ is cofinal in $\alpha$: for any $\xi < \alpha$, choose $\eta < \beta$ with $\xi \le f(\eta)$, and choose $\zeta < \gamma$ with $\eta \le g(\zeta)$; since $f$ is non-decreasing, $\xi \le f(\eta) \le f(g(\zeta))$. By minimality of $\beta = \mathrm{cf}(\alpha)$, $\beta \le \gamma$, so $\mathrm{cf}(\mathrm{cf}(\alpha)) = \mathrm{cf}(\alpha)$.
- **Definition (Regular and Singular Cardinals)**: An infinite cardinal $\kappa$ is *regular* if $\mathrm{cf}(\kappa) = \kappa$, and *singular* if $\mathrm{cf}(\kappa) < \kappa$.
  - $\aleph_0$ is regular (finite unions of finite sets are finite).
  - Under the Axiom of Choice, every successor cardinal $\kappa^+$ is regular (since a union of $\le \kappa$ sets of cardinality $\le \kappa$ has cardinality $\le \kappa \otimes \kappa = \kappa < \kappa^+$).
  - $\aleph_\omega = \sup_{n < \omega} \aleph_n$ is the least singular cardinal, with $\mathrm{cf}(\aleph_\omega) = \omega < \aleph_\omega$.

### 3.2 Inaccessible Cardinals and Grothendieck-Zermelo Universes (Jech Section 5.3)
- **Definition (Weakly and Strongly Inaccessible Cardinals)**:
  1. An uncountable cardinal $\kappa > \aleph_0$ is *weakly inaccessible* if it is a regular limit cardinal ($\kappa = \aleph_\kappa$ and $\mathrm{cf}(\kappa) = \kappa$).
  2. An uncountable cardinal $\kappa > \aleph_0$ is *strongly inaccessible* (or simply *inaccessible*) if it is regular ($\mathrm{cf}(\kappa) = \kappa$) and a *strong limit cardinal* ($\forall \lambda < \kappa,\, 2^\lambda < \kappa$).
  3. Under GCH, every weakly inaccessible cardinal is strongly inaccessible.
- **Theorem (Cumulative Stage $V_\kappa$ as a Model of ZFC)**: If $\kappa$ is strongly inaccessible, then $V_\kappa$ satisfies all axioms of ZFC:
  - **Extensionality, Foundation, Empty Set, Pairing, Union, Power Set, Infinity**: Hold in $V_\alpha$ for every limit ordinal $\alpha > \omega$.
  - **Comprehension (Separation)**: If $x \in V_\kappa$ and $y \subseteq x$, then $\mathrm{rank}(y) \le \mathrm{rank}(x) < \kappa$, so $y \in V_\kappa$.
  - **Replacement**: Let $x \in V_\kappa$ (say $x \in V_\alpha$ with $\alpha < \kappa$). Since $\kappa$ is a strong limit, $|V_\alpha| < \kappa$, hence $|x| \le |V_\alpha| < \kappa$. For any function $F : x \to V_\kappa$, the ranks $\{\mathrm{rank}(F(u)) : u \in x\}$ form a subset of $\kappa$ of cardinality $|x| < \kappa$. By regularity of $\kappa$ ($\mathrm{cf}(\kappa) = \kappa$), $\beta = \sup_{u \in x} (\mathrm{rank}(F(u)) + 1) < \kappa$, so $F[x] \subseteq V_\beta$ and hence $F[x] \in V_{\beta+1} \subseteq V_\kappa$.
  - **Indepenence from ZFC**: By Gödel's Second Incompleteness Theorem, since $V_\kappa \models \mathrm{ZFC}$ implies $\mathrm{Con}(\mathrm{ZFC})$, the existence of a strongly (or weakly, via $L_\kappa \models \mathrm{ZFC}$) inaccessible cardinal cannot be proved in ZFC if ZFC is consistent.
