# Theorem and Exercise Index for Jech Set Theory Archive

This document catalogs all formal theorems, lemmas, corollaries, definitions, axioms, worked examples, and exercises across `/botworkspace/Jech`, accompanying Thomas Jech's *Set Theory* (3rd Millennium Edition).

## 1. Summary of Formalized Modules

| File | System / Language | Scope and Mathematical Contents | Formal Items |
| :--- | :--- | :--- | :--- |
| [Jech.v](file:///botworkspace/Jech/Jech.v) | Coq | First-Order Logic AST (`Fo`), worked examples, syntactic node measure `size`, structural induction lemma `size_ge_one`, and Axiom of Infinity (`axInfty`) walkthrough | 14 |
| [Part_III.v](file:///botworkspace/Jech/Part_III.v) | Coq | First-Order Logic `Var`, `Term`, `Formula`, substitution `SubstTerm` and `Subst`, Hilbert calculus `Haxiom` and `Proof`, Tarski semantics `Sat`, and `soundness` theorem | 21 |
| [section_mostowski.v](file:///botworkspace/Jech/section_mostowski.v) | Coq | Well-founded extensional relations, transitive closure, ordinal rank trees, Aczel-style sets `MSet`, Mostowski Collapse Theorem (`mostowski_transitive`, `mostowski_injective`, `mostowski_isomorphism`, `mostowski_uniqueness`), and finite von Neumann ordinals | 42 |
| [section_cumulative_hierarchy.v](file:///botworkspace/Jech/section_cumulative_hierarchy.v) | Coq | Cumulative hierarchy stages $V_\alpha$, transitivity and monotonicity, ordinal rank on `MSet`, Axiom of Foundation equivalence $V = \bigcup_\alpha V_\alpha$, $\Delta_0$ formulas, Lévy absoluteness, and Montague-Lévy Reflection | 46 |
| [section_choice.v](file:///botworkspace/Jech/section_choice.v) | Coq | Posets, chains, Zorn's Lemma, Zermelo's Well-Ordering Theorem, Axiom of Choice, Cartesian product non-emptiness, Teichmüller-Tukey Lemma, and full equivalence cycle | 54 |
| [section_ex_1_6.v](file:///botworkspace/Jech/section_ex_1_6.v) | Coq | Jech Chapter 1 Exercise 1.6: transitive sets whose non-empty subsets have $\in$-minimal elements (`prop_1_6`, `ex_1_6_lem1` through `ex_1_6_lem5`, `ex_1_6_zero`, and `ex_1_6`) | 10 |
| [src/axioms/axInfty.v](file:///botworkspace/Jech/src/axioms/axInfty.v) | Coq | Constructive derivation of the Axiom of Infinity (`axInfty`) via impredicative `sup` trees | 7 |
| [src/axioms/axRep.v](file:///botworkspace/Jech/src/axioms/axRep.v) | Coq | Constructive derivation of the Axiom of Replacement (`axRep_image`) via `sup` trees | 7 |
| [proofs/axRep_axInfty_proofs.ML](file:///botworkspace/Jech/proofs/axRep_axInfty_proofs.ML) | Standard ML (Poly/ML) | Executable set-tree model (`ens`) verifying extensionality, successor closure, `verify_replacement`, and `verify_infinity` | 15 |
| [jech/mostowski.py](file:///botworkspace/Jech/jech/mostowski.py) | Python | Executable verification of well-foundedness, extensionality, transitive closure, rank, and Mostowski collapse isomorphism | 14 |
| [jech/cumulative_hierarchy.py](file:///botworkspace/Jech/jech/cumulative_hierarchy.py) | Python | Executable cumulative hierarchy stages $V_n$, rank computation, Foundation check, and $\Delta_0$ / Tarski-Vaught reflection | 22 |
| [jech/choice_zorn.py](file:///botworkspace/Jech/jech/choice_zorn.py) | Python | Executable verification of choice functions, partial/linear/well-orders, Zorn's Lemma, and Teichmüller-Tukey finite character | 18 |
| [jech/first_order_logic.py](file:///botworkspace/Jech/jech/first_order_logic.py) | Python | First-order formula parser, finite model evaluator, and Hilbert-style proof checker | 6 |

---

## 2. Core Coq Formalizations

### 2.1 First-Order Logic AST and Meta-Theory ([Jech.v](file:///botworkspace/Jech/Jech.v))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Inductive | `Fo` | [L93](file:///botworkspace/Jech/Jech.v#L93-L112) | First-order formula syntax: `Pred`, `Eq`, `And`, `Or`, `Imp`, `Not`, `Forall`, `Exists` | Verified |
| Example | `predicate_example` | [L146](file:///botworkspace/Jech/Jech.v#L146) | Atomic predicate formula `Pred 1 [2; 3]` | Verified |
| Example | `equality_example` | [L149](file:///botworkspace/Jech/Jech.v#L149) | Atomic equality formula `Eq 2 3` | Verified |
| Example | `and_example` | [L154](file:///botworkspace/Jech/Jech.v#L154) | Conjunction `And (Eq 2 3) (Pred 1 [2; 3])` | Verified |
| Example | `or_example` | [L157](file:///botworkspace/Jech/Jech.v#L157) | Disjunction `Or (Eq 2 3) (Pred 1 [2; 3])` | Verified |
| Example | `imp_example` | [L160](file:///botworkspace/Jech/Jech.v#L160) | Implication `Imp (Eq 2 3) (Pred 1 [2; 3])` | Verified |
| Example | `not_example` | [L163](file:///botworkspace/Jech/Jech.v#L163) | Negation `Not (Eq 2 3)` | Verified |
| Example | `forall_example` | [L168](file:///botworkspace/Jech/Jech.v#L168) | Universal quantification `Forall 1 (Eq 1 2)` | Verified |
| Example | `exists_example` | [L171](file:///botworkspace/Jech/Jech.v#L171) | Existential quantification `Exists 1 (Eq 1 2)` | Verified |
| Example | `nested_example` | [L175](file:///botworkspace/Jech/Jech.v#L175-L176) | Nested formula `Forall 2 (Imp (Eq 2 3) (Exists 1 (Pred 1 [1; 3])))` | Verified |
| Fixpoint | `size` | [L194](file:///botworkspace/Jech/Jech.v#L194-L204) | Recursive syntactic node count `size : Fo -> nat` | Verified |
| Lemma | `size_ge_one` | [L211](file:///botworkspace/Jech/Jech.v#L211-L216) | `forall f : Fo, 1 <= size f` | Verified (`Qed`) |
| Example | `size_of_and_example` | [L221](file:///botworkspace/Jech/Jech.v#L221-L222) | `size and_example = 3` | Verified (`Qed`) |
| Example | `size_ge_one_and_example` | [L225](file:///botworkspace/Jech/Jech.v#L225) | `1 <= size and_example` | Verified |

### 2.2 Hilbert Calculus and Soundness ([Part_III.v](file:///botworkspace/Jech/Part_III.v))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Inductive | `Var`, `Term`, `Formula` | [L12](file:///botworkspace/Jech/Part_III.v#L12-L29) | First-order variables, terms (`VarTerm`, `FuncTerm`), and formulas | Verified |
| Fixpoint | `SubstTerm`, `Subst` | [L33](file:///botworkspace/Jech/Part_III.v#L33-L65) | Syntactic term and formula substitution | Verified |
| Inductive | `Haxiom` | [L70](file:///botworkspace/Jech/Part_III.v#L70-L78) | Hilbert axiom schemas `Haxiom1` through `Haxiom8` | Verified |
| Inductive | `Proof` | [L82](file:///botworkspace/Jech/Part_III.v#L82-L85) | Hilbert derivability via `AxiomProof`, Modus Ponens (`MP`), and Generalization (`Gen`) | Verified |
| Fixpoint | `eval_term`, `Sat` | [L102](file:///botworkspace/Jech/Part_III.v#L102-L120) | Tarski term evaluation and satisfaction relation `Sat (e : env) (F : Formula) : Prop` | Verified |
| Lemma | `haxiom1_sound` | [L124](file:///botworkspace/Jech/Part_III.v#L124-L128) | Soundness of equality symmetry axiom | Verified (`Qed`) |
| Lemma | `haxiom2_sound` | [L130](file:///botworkspace/Jech/Part_III.v#L130-L134) | Soundness of Frege implication distribution axiom $(P \implies (Q \implies R)) \implies ((P \implies Q) \implies (P \implies R))$ | Verified (`Qed`) |
| Lemma | `haxiom3_sound` | [L136](file:///botworkspace/Jech/Part_III.v#L136-L140) | Soundness of left conjunction elimination $(P \land Q) \implies P$ | Verified (`Qed`) |
| Lemma | `haxiom4_sound` | [L142](file:///botworkspace/Jech/Part_III.v#L142-L146) | Soundness of right conjunction elimination $(P \land Q) \implies Q$ | Verified (`Qed`) |
| Lemma | `haxiom5_sound` | [L148](file:///botworkspace/Jech/Part_III.v#L148-L152) | Soundness of conjunction introduction $P \implies (Q \implies (P \land Q))$ | Verified (`Qed`) |
| Lemma | `haxiom6_sound` | [L154](file:///botworkspace/Jech/Part_III.v#L154-L158) | Soundness of contraposition $(P \implies Q) \implies ((Q \implies P) \implies (\neg P \implies \neg Q))$ | Verified (`Qed`) |
| Axiom | `haxiom7_sound` | [L161](file:///botworkspace/Jech/Part_III.v#L161-L162) | Soundness of universal instantiation $(\forall x, P) \implies P[x := x]$ (completed in [exercise_1_6_and_fol_substitution_completion.md](file:///botworkspace/Jech/notes/exercise_1_6_and_fol_substitution_completion.md)) | Postulated (`Axiom`) |
| Axiom | `haxiom8_sound` | [L164](file:///botworkspace/Jech/Part_III.v#L164-L165) | Soundness of self-substitution specialization $(P[x := x] \implies \forall x, P) \implies \forall x, P$ (completed in [exercise_1_6_and_fol_substitution_completion.md](file:///botworkspace/Jech/notes/exercise_1_6_and_fol_substitution_completion.md)) | Postulated (`Axiom`) |
| Lemma | `haxiom_sound` | [L167](file:///botworkspace/Jech/Part_III.v#L167-L179) | `forall F, Haxiom F -> forall e : env, Sat e F` | Verified (`Qed`) |
| Theorem | `soundness` | [L182](file:///botworkspace/Jech/Part_III.v#L182-L196) | `forall F, Proof F -> forall e : env, Sat e F` | Verified (`Qed`) |

### 2.3 Well-Founded Relations, Ordinal Rank, and Mostowski Collapse ([section_mostowski.v](file:///botworkspace/Jech/section_mostowski.v))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Definition | `extensional`, `is_minimal` | [L33](file:///botworkspace/Jech/section_mostowski.v#L33-L37) | Extensionality and $E$-minimality for binary relation $E$ on $A$ | Verified |
| Theorem | `well_founded_induction_principle` | [L39](file:///botworkspace/Jech/section_mostowski.v#L39-L47) | Transfinite induction along well-founded relation $E$ | Verified (`Qed`) |
| Definition | `in_TC`, `TC_set` | [L53](file:///botworkspace/Jech/section_mostowski.v#L53-L55) | Transitive closure membership via `clos_trans A E` | Verified |
| Lemma | `TC_step`, `TC_trans`, `TC_is_transitive` | [L57](file:///botworkspace/Jech/section_mostowski.v#L57-L78) | Base inclusion, transitivity, and step closure of transitive closure | Verified (`Qed`) |
| Theorem | `wf_TC` | [L80](file:///botworkspace/Jech/section_mostowski.v#L80-L85) | `well_founded E -> well_founded (clos_trans A E)` | Verified (`Qed`) |
| Inductive | `Ord`, `OLess` | [L95](file:///botworkspace/Jech/section_mostowski.v#L95-L103) | Brouwer-style ordinal trees (`OZero`, `OSucc`, `OLim`) and strict ordering | Verified |
| Fixpoint | `rank_acc`, `rank` | [L111](file:///botworkspace/Jech/section_mostowski.v#L111-L137) | Accessibility-guarded ordinal rank $\mathrm{rank}(x) = \sup\{\mathrm{rank}(y) + 1 : y \mathrel{E} x\}$ | Verified |
| Lemma | `rank_acc_irrel`, `rank_eq_acc`, `rank_unfold` | [L118](file:///botworkspace/Jech/section_mostowski.v#L118-L160) | Proof irrelevance of accessibility witnesses and unfolding equation for `rank` | Verified (`Qed`) |
| Theorem | `rank_strictly_increasing` | [L162](file:///botworkspace/Jech/section_mostowski.v#L162-L176) | `forall x y : A, E y x -> OLess (rank y) (rank x)` | Verified (`Qed`) |
| Inductive | `MSet` | [L183](file:///botworkspace/Jech/section_mostowski.v#L183-L192) | Aczel-style set trees `mset : forall A : Type, (A -> MSet) -> MSet` with `In_MSet` and `is_transitive` | Verified |
| Fixpoint | `pi_acc`, `pi` | [L200](file:///botworkspace/Jech/section_mostowski.v#L200-L225) | Mostowski collapse function $\pi(x) = \{\pi(y) : y \mathrel{E} x\}$ | Verified |
| Lemma | `pi_acc_irrel`, `pi_eq_acc`, `pi_unfold` | [L207](file:///botworkspace/Jech/section_mostowski.v#L207-L245) | Accessibility proof irrelevance and recursive unfolding of $\pi$ | Verified (`Qed`) |
| Lemma | `pi_rel_forward`, `pi_rel_backward` | [L247](file:///botworkspace/Jech/section_mostowski.v#L247-L267) | Forward and backward preservation of membership under $\pi$ | Verified (`Qed`) |
| Theorem | `mostowski_transitive` | [L272](file:///botworkspace/Jech/section_mostowski.v#L272-L279) | `is_transitive M_image` (the Mostowski collapse image is transitive) | Verified (`Qed`) |
| Theorem | `mostowski_injective` | [L281](file:///botworkspace/Jech/section_mostowski.v#L281-L310) | `extensional A E -> forall x y : A, pi x = pi y -> x = y` | Verified (`Qed`) |
| Theorem | `mostowski_isomorphism` | [L312](file:///botworkspace/Jech/section_mostowski.v#L312-L325) | `extensional A E -> forall x y : A, E y x <-> In_MSet (pi y) (pi x)` | Verified (`Qed`) |
| Theorem | `mostowski_uniqueness` | [L327](file:///botworkspace/Jech/section_mostowski.v#L327-L345) | Uniqueness of the Mostowski collapse map $\pi$ | Verified (`Qed`) |
| Lemma | `empty_MSet_no_elements`, `in_singleton_MSet`, `in_pair_MSet_left`, `in_pair_MSet_right`, `vn_0_in_vn_1`, `vn_1_in_vn_2`, `vn_0_in_vn_2` | [L353](file:///botworkspace/Jech/section_mostowski.v#L353-L402) | Properties of $\emptyset, \{s\}, \{s_1, s_2\}$ and finite von Neumann ordinals $0, 1, 2$ | Verified (`Qed`) |

### 2.4 Cumulative Hierarchy, Foundation, and Reflection ([section_cumulative_hierarchy.v](file:///botworkspace/Jech/section_cumulative_hierarchy.v))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Inductive | `In_V` | [L35](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L35-L43) | Cumulative hierarchy stage membership $x \in V_\alpha$ | Verified |
| Theorem | `V_0_empty`, `empty_in_V_succ`, `V_succ_power`, `V_lim_union` | [L45](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L45-L92) | $V_0 = \emptyset$, $\emptyset \in V_{\alpha+1}$, $V_{\alpha+1} = \mathcal{P}(V_\alpha)$, $V_\lambda = \bigcup_{\beta < \lambda} V_\beta$ | Verified (`Qed`) |
| Theorem | `stage_trans_and_succ_mono`, `V_alpha_transitive`, `V_monotonic` | [L117](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L117-L179) | Every stage $V_\alpha$ is transitive and $\alpha \le \beta \implies V_\alpha \subseteq V_\beta$ | Verified (`Qed`) |
| Theorem | `rank_strictly_increasing_In_MSet`, `mset_in_succ_rank` | [L200](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L200-L218) | $y \in x \implies \mathrm{rank}(y) < \mathrm{rank}(x)$ and $x \in V_{\mathrm{rank}(x)+1}$ | Verified (`Qed`) |
| Theorem | `In_MSet_wf`, `no_self_membership`, `no_2_cycle`, `no_3_cycle`, `no_infinite_descent` | [L263](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L263-L320) | Well-foundedness of `In_MSet`, absence of $\in$-cycles and infinite descending chains | Verified (`Qed`) |
| Theorem | `V_equals_Union_V_alpha`, `cumulative_hierarchy_implies_well_founded`, `foundation_and_hierarchy_equivalence` | [L331](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L331-L366) | Equivalence of the Axiom of Foundation and $V = \bigcup_\alpha V_\alpha$ (Jech Theorem 6.6) | Verified (`Qed`) |
| Inductive | `SetFormula`, `is_Delta0` | [L373](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L373-L393) | Set-theoretic formula AST and $\Delta_0$ bounded quantifier classification | Verified |
| Theorem | `Delta0_absoluteness`, `Delta0_stage_reflection`, `Delta0_all_stages_reflect` | [L428](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L428-L532) | Upward and downward absoluteness of $\Delta_0$ formulas for transitive classes and $V_\alpha$ | Verified (`Qed`) |
| Theorem | `Reflects_Not`, `Reflects_And`, `Reflects_Or`, `Reflects_Imp`, `Tarski_Vaught_reflection_step_Ex`, `cumulative_limit_continuous` | [L534](file:///botworkspace/Jech/section_cumulative_hierarchy.v#L534-L612) | Closure of reflection under connectives, Tarski-Vaught existential criterion, and limit continuity (Jech Theorem 12.14) | Verified (`Qed`) |

### 2.5 Axiom of Choice, Zorn's Lemma, Well-Ordering, and Tukey's Lemma ([section_choice.v](file:///botworkspace/Jech/section_choice.v))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Lemma | `empty_is_chain`, `singleton_is_chain`, `pair_chain_le` | [L65](file:///botworkspace/Jech/section_choice.v#L65-L95) | Elementary chain properties in partial orders | Verified (`Qed`) |
| Lemma | `least_element_unique` | [L130](file:///botworkspace/Jech/section_choice.v#L130-L142) | Uniqueness of the least element of a subset in a well-order | Verified (`Qed`) |
| Lemma | `empty_MSet_has_choice_function`, `singleton_MSet_empty_choice`, `von_neumann_0_choice`, `von_neumann_1_choice`, `von_neumann_2_choice` | [L168](file:///botworkspace/Jech/section_choice.v#L168-L212) | Constructive choice functions for finite families and von Neumann ordinals | Verified (`Qed`) |
| Theorem | `AC_to_cartesian_product`, `cartesian_product_to_AC`, `AC_iff_cartesian_product` | [L227](file:///botworkspace/Jech/section_choice.v#L227-L276) | Equivalence of Relational Choice and non-emptiness of Cartesian products of non-empty families | Verified (`Qed`) |
| Theorem | `relational_choice_implies_MSet_choice` | [L278](file:///botworkspace/Jech/section_choice.v#L278-L302) | Relational Choice implies existence of set-level choice functions on `MSet` | Verified (`Qed`) |
| Theorem | `Zorn_implies_relational_choice`, `Zorn_implies_MSet_choice`, `Tukey_implies_relational_choice`, `WO_implies_relational_choice`, `relational_choice_implies_WO`, `relational_choice_implies_Zorn`, `WO_implies_Zorn`, `Zorn_implies_WO`, `Zorn_implies_Tukey` | [L357](file:///botworkspace/Jech/section_choice.v#L357-L423) | Directed implications among AC, Zorn's Lemma, Well-Ordering Theorem, and Teichmüller-Tukey Lemma | Verified (`Qed`) |
| Theorem | `choice_zorn_equivalence`, `choice_wo_equivalence`, `zorn_wo_equivalence`, `choice_tukey_equivalence` | [L425](file:///botworkspace/Jech/section_choice.v#L425-L455) | Biconditional equivalences (Jech Chapter 5: $\mathrm{AC} \iff \mathrm{Zorn} \iff \mathrm{WO} \iff \mathrm{Tukey}$) | Verified (`Qed`) |

### 2.6 Jech Chapter 1, Exercise 1.6 ([section_ex_1_6.v](file:///botworkspace/Jech/section_ex_1_6.v))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Definition | `prop_1_6`, `PP` | [L13](file:///botworkspace/Jech/section_ex_1_6.v#L13-L74) | $x$ is transitive and every non-empty subset $z \subseteq x$ has an $\in$-minimal element | Verified |
| Lemma | `ex_1_6_lem1`, `ex_1_6_lem1'` | [L27](file:///botworkspace/Jech/section_ex_1_6.v#L27-L61) | `SoundPred prop_1_6` (extensional invariance of `prop_1_6`) | Verified (`Qed`) |
| Lemma | `ex_1_6_lem2` | [L91](file:///botworkspace/Jech/section_ex_1_6.v#L91-L109) | `~ IN y y` for any transitive $y$ satisfying `PP y` | Verified (`Qed`) |
| Lemma | `ex_1_6_lem3` | [L115](file:///botworkspace/Jech/section_ex_1_6.v#L115-L120) | `IN a y -> ~ IN y a` | Verified (`Qed`) |
| Lemma | `ex_1_6_lem4` | [L127](file:///botworkspace/Jech/section_ex_1_6.v#L127-L154) | `epsmin m z -> epsmin m (Union (Pair z (Sing y)))` | Verified (`Qed`) |
| Lemma | `ex_1_6_lem5` | [L161](file:///botworkspace/Jech/section_ex_1_6.v#L161-L175) | `PP (Sing y)` | Verified (`Qed`) |
| Theorem | `ex_1_6_zero` | [L182](file:///botworkspace/Jech/section_ex_1_6.v#L182-L205) | `IN Vide (Comp X prop_1_6)` | Partial |
| Theorem | `ex_1_6` | [L212](file:///botworkspace/Jech/section_ex_1_6.v#L212-L216) | `Ind (Comp X prop_1_6)` (completed in [exercise_1_6_and_fol_substitution_completion.md](file:///botworkspace/Jech/notes/exercise_1_6_and_fol_substitution_completion.md)) | `Admitted` |

### 2.7 Standalone Axiom & Example Sketches ([src/axioms/](file:///botworkspace/Jech/src/axioms) and [examples/](file:///botworkspace/Jech/examples))

- [src/axioms/axInfty.v](file:///botworkspace/Jech/src/axioms/axInfty.v): `Theorem axInfty` proving $\exists Y,\, \forall z,\, z \in Y \iff \exists n : \mathrm{nat},\, z = \mathrm{Nat}(n)$ via `sup nat Nat`.
- [src/axioms/axRep.v](file:///botworkspace/Jech/src/axioms/axRep.v): `Theorem axRep_image` proving existence of the replacement image `sup A f` for any type $A$ and mapping $f : A \to \mathrm{Ens}$.
- [examples/example_3.v](file:///botworkspace/Jech/examples/example_3.v): `Theorem intersection` and `Theorem difference` over characteristic predicates.
- [examples/example_4.v](file:///botworkspace/Jech/examples/example_4.v): `Example formulas_well_formed` for `infinity_formula` and `power_set_formula`.
- [examples/example_6.v](file:///botworkspace/Jech/examples/example_6.v): `Theorem power_set_fo_valid` and `Theorem power_set_pred_exists`.
- [examples/example_7.v](file:///botworkspace/Jech/examples/example_7.v): `Theorem union_fo_valid` and `Theorem union_predicate_exists` (accompanied by [notes/union_derivation.md](file:///botworkspace/Jech/notes/union_derivation.md)).
- [examples/example_8.v](file:///botworkspace/Jech/examples/example_8.v): `Theorem regularity_fo_valid` and `Theorem zero_minimal_regularity`.
- [examples/example_9.v](file:///botworkspace/Jech/examples/example_9.v): `Theorem choice_fo_valid` and `Theorem choice_functional`.
- [examples/example_10.v](file:///botworkspace/Jech/examples/example_10.v): `Theorem union_axiom_example`.
- [notes/exercise_1_6_and_fol_substitution_completion.md](file:///botworkspace/Jech/notes/exercise_1_6_and_fol_substitution_completion.md): Complete formal proof notes and completions for `ex_1_6`, `haxiom7_sound`, `haxiom8_sound`, cofinality, and inaccessible cardinals.
