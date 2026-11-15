# Jech `purgatorium/` Formal Proof Solutions and Mathematical Notes

This document catalogs and resolves all unfinished proofs, `Abort` blocks, `admit` goals, and `TODO` annotations inside `/botworkspace/Jech/purgatorium/` (as tracked in Section V.2 of `/botworkspace/forgotten.txt`). The machine-checked, zero-`Admitted` Coq formalizations of these solutions live in [purgatorium/purgatorium_completions.v](file:///botworkspace/Jech/purgatorium/purgatorium_completions.v).

---

## 1. Intensional vs. Extensional Equality and Comprehension Soundness (`purgatorium/_CEX.v`)

### 1.1 Problem Context
In [purgatorium/_CEX.v](file:///botworkspace/Jech/purgatorium/_CEX.v#L18-L275), two empty sets with distinct index types are defined in the Scott-Aczel `Ens` tree model:
$$S_1 := \mathrm{sup}(\mathrm{unit}, \lambda \_.\, \mathrm{Vide}), \qquad S_2 := \mathrm{sup}(\mathrm{bool}, \lambda \_.\, \mathrm{Vide}).$$
Wait-free inspection shows:
1. $S_1 \neq S_2$ intensionally (`Theorem uneb` / `S1_neq_S2`), because an equality of inductive `sup` trees would induce a type equality $\mathrm{bool} = \mathrm{unit}$ and thus an injection from $\mathrm{bool}$ into $\mathrm{unit}$, contradicting $\mathrm{true} \neq \mathrm{false}$.
2. $\mathrm{EQ}(S_1, S_2)$ holds extensionally (`Theorem ESS`), because for every $z : \mathrm{Ens}$, neither $S_1$ nor $S_2$ has any member ($\mathrm{Vide}$ is empty, Wait: both $S_1$ and $S_2$ contain $\mathrm{Vide}$ as their sole member, so both represent $\{\emptyset\}$).

In `_CEX.v` lines 108--130 (`Comp_not_sound_right`), lines 180--199 (`Comp_not_sound_left`), and line 261 (`assert (J: IN e S1). admit.`), the file attempted to construct an explicit counterexample showing that raw restricted comprehension
$$\mathrm{Comp}(E, P) = \mathrm{sup}\left(\{a : A \mid P(f(a))\}, \lambda s.\, f(\pi_1(s))\right)$$
fails to respect extensional equality $\mathrm{EQ}$ when $P : \mathrm{Ens} \to \mathrm{Prop}$ is an **intensional** predicate that does not respect $\mathrm{EQ}$.

### 1.2 Mathematical Resolution and Formal Proof
Define the intensional predicate:
$$P_{\mathrm{int}}(w) :\Longleftrightarrow (w = S_1)$$
using Coq's intensional Leibniz equality (`=`).
- Since $\mathrm{EQ}(S_1, S_2)$, the singletons $x_1 := \mathrm{Sing}(S_1)$ and $x_2 := \mathrm{Sing}(S_2)$ satisfy $\mathrm{EQ}(x_1, x_2)$ (`Sing_sound`).
- Evaluating $\mathrm{Comp}(x_1, P_{\mathrm{int}})$ keeps the element $S_1$ because $S_1 = S_1$ holds reflexivity, so $\mathrm{IN}(S_1, \mathrm{Comp}(\mathrm{Sing}(S_1), P_{\mathrm{int}}))$.
- Evaluating $\mathrm{Comp}(x_2, P_{\mathrm{int}})$ filters the two boolean copies of $S_2$ by the condition $S_2 = S_1$. Because $S_1 \neq S_2$, the comprehension subtype $\{b : \mathrm{bool} \mid S_2 = S_1\}$ is uninhabited. Thus $\mathrm{Comp}(\mathrm{Sing}(S_2), P_{\mathrm{int}})$ has no elements, and $\neg \mathrm{IN}(S_1, \mathrm{Comp}(\mathrm{Sing}(S_2), P_{\mathrm{int}}))$.
- By the Axiom of Extensionality (`axExt`), $\neg \mathrm{EQ}(\mathrm{Comp}(x_1, P_{\mathrm{int}}), \mathrm{Comp}(x_2, P_{\mathrm{int}}))$.

Conversely, when $c, c_1, c_2 : \mathrm{Ens} \to \mathrm{Prop}$ are **extensionality-sound** ($\forall a\,b,\, \mathrm{EQ}(a, b) \implies (c(a) \iff c(b))$), both `Comp_sound_left` and `Comp_sound_right` hold:
$$\mathrm{EQ}(x_1, x_2) \implies \mathrm{EQ}(\mathrm{Comp}(x_1, c), \mathrm{Comp}(x_2, c)), \qquad \mathrm{EQC}(c_1, c_2) \implies \mathrm{EQ}(\mathrm{Comp}(x, c_1), \mathrm{Comp}(x, c_2)).$$
All of these theorems (`intensional_pred_unsound`, `Comp_not_sound_left_counterexample`, `Comp_sound_left`, and `Comp_sound_right`) are proved constructively in [purgatorium/purgatorium_completions.v](file:///botworkspace/Jech/purgatorium/purgatorium_completions.v#L219-L361).

---

## 2. Class Operations Transferred to Sets, Unsound Class Properties, and Domain of a Set Relation (`purgatorium/HHJJJKKLKLKLK.v` & `purgatorium/Jech_NOTATIONS.v`)

### 2.1 Problem Context
In [purgatorium/HHJJJKKLKLKLK.v](file:///botworkspace/Jech/purgatorium/HHJJJKKLKLKLK.v) and [purgatorium/Jech_NOTATIONS.v](file:///botworkspace/Jech/purgatorium/Jech_NOTATIONS.v):
- Line 32 (`HHJJJKKLKLKLK.v`) & Line 97 (`Jech_NOTATIONS.v`): `(* TODO Define operation on a class and transfer it to sets. *)`
- Line 372 (`HHJJJKKLKLKLK.v`): `(* ToDo: Find unsound class property. *)` (`cprty_unsound`)
- Lines 691--700 (`HHJJJKKLKLKLK.v`): `Theorem domias (R:Ens) : (ias (cDom R)). ... Abort.`

### 2.2 Mathematical Resolution and Formal Proof
1. **General Class-to-Set Transfer Principle (`scosias`)**:
   A well-defined class is a record `class := { prty : Ens -> Prop; sound : forall a b, EQ a b -> prty a -> prty b }`. The predicate `ias (C : class) : Prop` asserts that $C$ is represented by a set:
   $$\mathrm{ias}(C) :\Longleftrightarrow \exists x : \mathrm{Ens},\, \forall w : \mathrm{Ens},\, C(w) \iff \mathrm{IN}(w, x).$$
   Whenever a class operation $F(\vec{X})$ applied to sets $\vec{x}$ is bounded by a bounding set $m(\vec{x})$ crafted from ZFC set constructors ($\forall w,\, F(\vec{x})(w) \implies \mathrm{IN}(w, m(\vec{x}))$), `scosias` transfers $F(\vec{x})$ to the set $\mathrm{Comp}(m(\vec{x}), F(\vec{x}))$.

2. **Unsound Second-Order Class Property (`cprty_unsound_resolved`)**:
   While every `C : class` is sound with respect to `EQ` on set elements, a second-order predicate `cprty : class -> Prop` need not be invariant under class extensional equivalence $\mathrm{EQC}(A, B) \Longleftrightarrow \forall z,\, A(z) \iff B(z)$. Specifically, coercing $S_1$ and $S_2$ to classes via $\mathrm{stoc}$ yields $\mathrm{EQC}(\mathrm{stoc}(S_1), \mathrm{stoc}(S_2))$ (`stoc_S1_EQC_S2`), while the intensional class property $\mathrm{cprty}(C) :\Longleftrightarrow (C = \mathrm{stoc}(S_1))$ holds for $\mathrm{stoc}(S_1)$ and not for $\mathrm{stoc}(S_2)$.

3. **Domain of a Set Relation is a Set (`domias`)**:
   In `HHJJJKKLKLKLK.v` line 694, the proof of `domias (R : Ens) : ias (cDom R)` was aborted because it attempted to use `cPow (cUnion (cUnion R))` instead of the bounding set $\bigcup \bigcup R = \mathrm{Union}(\mathrm{Union}(R))$.
   With Kuratowski ordered pairs $\mathrm{OrdPair}(u, v) = \{\{u\}, \{u, v\}\}$:
   - If $\mathrm{IN}(\mathrm{OrdPair}(u, v), R)$, then since $\mathrm{IN}(\mathrm{Sing}(u), \mathrm{OrdPair}(u, v))$, we have $\mathrm{IN}(\mathrm{Sing}(u), \mathrm{Union}(R))$.
   - Since $\mathrm{IN}(u, \mathrm{Sing}(u))$, a second union application yields $\mathrm{IN}(u, \mathrm{Union}(\mathrm{Union}(R)))$ (`OrdPair_fst_in_Union_Union`).
   - Applying `scosias` with bounding set $m = \mathrm{Union}(\mathrm{Union}(R))$ immediately proves `domias : forall R : Ens, ias (cDom R)` ([purgatorium/purgatorium_completions.v](file:///botworkspace/Jech/purgatorium/purgatorium_completions.v#L469-L487)).

---

## 3. Cartesian Products and the Axiom of Choice in `Ens` (`purgatorium/choice_DIFFERENT_VARIANTS.v` & `purgatorium/other_AC_stuff.v`)

### 3.1 Problem Context
In [purgatorium/choice_DIFFERENT_VARIANTS.v](file:///botworkspace/Jech/purgatorium/choice_DIFFERENT_VARIANTS.v#L186-L197) and [purgatorium/other_AC_stuff.v](file:///botworkspace/Jech/purgatorium/other_AC_stuff.v#L51-L101):
- `Product_IN` and the soundness obligation for choice graphs were left as `admit.`
- In `other_AC_stuff.v` line 74, extracting a witness in `pi1 (Union S)` from a witness $v$ satisfying $\mathrm{IN}(v, \pi_2(S, a))$ was left as `admit.`, and `ac_lem` was aborted.

### 3.2 Mathematical Resolution and Formal Proof
1. **Constructive Cartesian Product (`Product_IN`)**:
   Defining $\mathrm{Product}(A, B) := \mathrm{sup}(\pi_1(A) \times \pi_1(B), \lambda p.\, \mathrm{OrdPair}(\pi_2(A, \mathrm{fst}(p)), \pi_2(B, \mathrm{snd}(p))))$, if $\mathrm{IN}(x, A)$ is witnessed by $a : \pi_1(A)$ with $\mathrm{EQ}(x, \pi_2(A, a))$ and $\mathrm{IN}(y, B)$ is witnessed by $b : \pi_1(B)$ with $\mathrm{EQ}(y, \pi_2(B, b))$, then $(a, b) : \pi_1(A) \times \pi_1(B)$ witnesses $\mathrm{IN}(\mathrm{OrdPair}(x, y), \mathrm{Product}(A, B))$ via `OrdPair_sound_both`.
2. **Total Choice Graph (`choifunc_total_completed`) and Union Inhabitation (`ac_lem_completed`)**:
   Given type-level relational choice `TypeRelationalChoice` and a family $S = \mathrm{sup}(T_S, f_S)$ of inhabited sets ($\forall X,\, \mathrm{IN}(X, S) \implies \exists q,\, \mathrm{IN}(q, X)$):
   - For each index $a : \pi_1(S)$, since $\mathrm{IN}(\pi_2(S, a), S)$ (`lem4`), there exists $q$ with $\mathrm{IN}(q, \pi_2(S, a))$.
   - By `IN_Union`, $\mathrm{IN}(q, \mathrm{Union}(S))$, which unpacks directly to an index $b : \pi_1(\mathrm{Union}(S))$ such that $\mathrm{EQ}(q, \pi_2(\mathrm{Union}(S), b))$, and hence $\mathrm{IN}(\pi_2(\mathrm{Union}(S), b), \pi_2(S, a))$.
   - Applying `TypeRelationalChoice` to $P(a, b) :\Longleftrightarrow \mathrm{IN}(\pi_2(\mathrm{Union}(S), b), \pi_2(S, a))$ yields a choice map $f : \pi_1(S) \to \pi_1(\mathrm{Union}(S))$.
   - Setting $\mathrm{chfu} := \mathrm{sup}(\pi_1(S), \lambda a.\, \mathrm{OrdPair}(\pi_2(S, a), \pi_2(\mathrm{Union}(S), f(a))))$, for every $X$ with $\mathrm{IN}(X, S)$, the chosen element $Q := \pi_2(\mathrm{Union}(S), f(a))$ satisfies both $\mathrm{IN}(\mathrm{OrdPair}(X, Q), \mathrm{chfu})$ and $\mathrm{IN}(Q, X)$ ([purgatorium/purgatorium_completions.v](file:///botworkspace/Jech/purgatorium/purgatorium_completions.v#L521-L579)).

---

## 4. Diaconescu's Theorem and Extensional Hilbert Epsilon (`purgatorium/copyDiaconescu.v`)

### 4.1 Problem Context
[purgatorium/copyDiaconescu.v](file:///botworkspace/Jech/purgatorium/copyDiaconescu.v#L1) opens with `(* TODO: try to prove LEM for Set. *)` and studies how the Axiom of Choice combined with Predicate Extensionality (or an extensional Hilbert $\varepsilon$-operator) entails the Law of Excluded Middle ($P \vee \neg P$).

### 4.2 Mathematical Resolution and Formal Proof
In [purgatorium/purgatorium_completions.v](file:///botworkspace/Jech/purgatorium/purgatorium_completions.v#L583-L645), both forms are proved completely without external dependencies:
1. `diaconescu_pred_ext_choice_imp_EM`: Given `PredicateExtensionality` on $\mathrm{bool} \to \mathrm{Prop}$ and a guarded relational choice selector $R$ on non-empty boolean predicates, for any proposition $P$ define:
   $$U(b) :\Longleftrightarrow (b = \mathrm{true} \vee P), \qquad V(b) :\Longleftrightarrow (b = \mathrm{false} \vee P).$$
   Since $U(\mathrm{true})$ and $V(\mathrm{false})$ hold, $R$ selects unique booleans $b_0$ for $U$ and $b_1$ for $V$. Case analysis on $U(b_0)$ and $V(b_1)$ either immediately yields a proof of $P$ (giving $\mathrm{left}\,P$), or else $b_0 = \mathrm{true}$ and $b_1 = \mathrm{false}$. In the latter case, assuming $P$ makes $U(b) \iff V(b)$ for all $b$, so `PredicateExtensionality` yields $U = V$, forcing $b_0 = b_1$ by uniqueness of $R$, which contradicts $\mathrm{true} \neq \mathrm{false}$ (giving $\mathrm{right}\,(\neg P)$).
2. `bell_extensional_epsilon_imp_EM`: Given an extensional selection operator $\varepsilon : (\mathrm{bool} \to \mathrm{Prop}) \to \mathrm{bool}$, applying $\varepsilon$ to $B(y) :\Longleftrightarrow (y = \mathrm{false} \vee P)$ and $C(y) :\Longleftrightarrow (y = \mathrm{true} \vee P)$ similarly yields $P \vee \neg P$.
