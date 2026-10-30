(* ========================================================================= *)
(*  Jech.v — Development of formulas and derivations (Part III)              *)
(*                                                                           *)
(*  Provenance: written & verified by "opencode/glm-5.3-flash-free"          *)
(*              (Capability Tier 1) for [Curated] Ticket 001:                *)
(*              "Improve Documentation".                                     *)
(*                                                                           *)
(*  The file compiles standalone with the standard library only:             *)
(*      coqc -Q . '' Jech.v          (see `make check` / .gitlab-ci.yml)     *)
(* ========================================================================= *)

(* ============================ FILE ROADMAP =============================== *)
(*                                                                           *)
(*  This file defines the inductive type `Fo` of first-order formulas,       *)
(*  illustrates every constructor with machine-checked `Example`s, and       *)
(*  demonstrates the standard proof style for this library (induction over   *)
(*  `Fo`) with the small verified lemma `size_ge_one`.                       *)
(*                                                                           *)
(*  Where to look next in this repository (cross-references):                *)
(*                                                                           *)
(*   - `Part_III.v`        : a parallel, Hilbert-style development of        *)
(*                           first-order syntax (`Var`, `Term`, `Formula`)   *)
(*                           plus axiom schemas and inference rules.  It     *)
(*                           requires this file via `Require Import Jech`.   *)
(*   - `axInfty.ML`        : Coq-style statement of the Axiom of Infinity    *)
(*                           (uses the `Ens`/`EQ`/`IN`/`Nat` prelude, so it  *)
(*                           is not standalone-checkable); the Poly/ML stub  *)
(*                           with companion notes lives in                   *)
(*                           `src/axioms/axInfty.ML` / `axInfty.md`.         *)
(*   - `src/axioms/*.ML`   : candidate axiom formalizations (`axRep.ML`,     *)
(*                           `axInfty.ML`) with companion `.md` notes.       *)
(*   - `proofs/*.ML`       : ground-truth proof terms                        *)
(*                           (`axRep_axInfty_proofs.ML`,                     *)
(*                           `zorn_wellordering_proofs.ML`) and the          *)
(*                           subtheories `proofs/subtheories/*.ML`; a second *)
(*                           variant of the same proof plus its test script  *)
(*                           lives in `src/proofs/axRep_axInfty.ML` and      *)
(*                           `src/proofs/test_axRep_axInfty.ML`.             *)
(*   - `examples/*.v`      : standalone usage sketches (informal; they are   *)
(*                           not part of the CI build, which runs on         *)
(*                           `Jech.v` only).                                 *)
(*   - `THEOREMS_INDEX.md` : high-level index of definitions and theorems.   *)
(*   - `DOCS.md` and `README.md` : narrative documentation of the library.   *)
(*                                                                           *)
(*  Naming convention: the previous revision of this file referenced         *)
(*  "Part_V / Theorem_1" and "Part_I / Definition_1"; no such objects exist  *)
(*  in the repository, so those stale cross-references were removed.         *)
(*                                                                           *)
(* ========================================================================= *)

(* First-order formulas use finite argument lists, so the standard list     *)
(* library and its textbook notations (`[x; y]`) are imported up front.     *)
Require Import List.          (* list notations `[x; y]` for argument lists *)
Require Import PeanoNat.      (* `Nat.le_0_l` used by `size_ge_one` below   *)
Import ListNotations.

Section Part_III.

(* ============================ THE FORMULA TYPE =========================== *)
(*                                                                           *)
(*  `Fo : Type` — abstract syntax trees for first-order formulas.            *)
(*                                                                           *)
(*  Design notes:                                                            *)
(*   - Variables, terms and predicate symbols are all encoded as plain       *)
(*     `nat` literals (`n`, `x`, `t1`, `t2`, ...).  This keeps `Fo` a        *)
(*     simple inductive type with one case per syntactic form, which makes   *)
(*     structural induction proofs short and uniform.  The trade-off is      *)
(*     that no scoping/typing invariant is enforced: e.g. `Forall x f` does  *)
(*     not check that `x` actually occurs free in `f`.  Callers that need    *)
(*     such invariants should compute free/bound variable sets first (see    *)
(*     the "possible extensions" note at the end of this file).              *)
(*   - All eight constructors are unambiguous, so `Fo` enjoys decidable      *)
(*     equality and can be decomposed directly by `destruct`/` induction`.   *)
(*                                                                           *)
(*  Related developments: `Part_III.v` defines the richer `Formula` type     *)
(*  (with distinct `Var`/`Term` sorts and explicit `True`/`False` cases)     *)
(*  used by the Hilbert-style derivation calculus.                          *)
(*                                                                           *)
(* ========================================================================= *)

Inductive Fo : Type :=
  (* `Pred n args`  — atomic predicate call: predicate symbol with        *)
  (*                  numeral `n`, applied to the argument list `args`.    *)
  (*                  Example shape:  P_1(2, 3)   ↦  Pred 1 [2; 3].        *)
  | Pred (n : nat) (args : list nat)
  (* `Eq t1 t2`     — atomic equality between two terms.                  *)
  (*                  Example shape:  2 = 3      ↦  Eq 2 3.               *)
  | Eq (t1 t2 : nat)
  (* `And f1 f2`    — conjunction  f1 ∧ f2.                               *)
  | And (f1 f2 : Fo)
  (* `Or f1 f2`     — disjunction  f1 ∨ f2.                               *)
  | Or (f1 f2 : Fo)
  (* `Imp f1 f2`    — implication  f1 ⇒ f2.                               *)
  | Imp (f1 f2 : Fo)
  (* `Not f`        — negation  ¬f.                                       *)
  | Not (f : Fo)
  (* `Forall x f`   — universal quantification  ∀x, f.                    *)
  | Forall (x : nat) (f : Fo)
  (* `Exists x f`   — existential quantification  ∃x, f.                  *)
  | Exists (x : nat) (f : Fo).

(* ========================= CONSTRUCTOR GLOSSARY ========================== *)
(*                                                                           *)
(*  | Constructor       | Meaning                 | Example term            | *)
(*  |-------------------|-------------------------|-------------------------| *)
(*  | `Pred n args`    | atomic predicate        | `Pred 1 [2; 3]`         | *)
(*  | `Eq t1 t2`       | atomic equality         | `Eq 2 3`                | *)
(*  | `And f1 f2`      | conjunction             | `And (Eq 2 3) f`        | *)
(*  | `Or f1 f2`       | disjunction             | `Or (Eq 2 3) f`         | *)
(*  | `Imp f1 f2`      | implication             | `Imp (Eq 2 3) f`        | *)
(*  | `Not f`          | negation                | `Not (Eq 2 3)`          | *)
(*  | `Forall x f`     | universal quantifier    | `Forall 1 (Eq 1 2)`     | *)
(*  | `Exists x f`     | existential quantifier  | `Exists 1 (Eq 1 2)`     | *)
(*                                                                           *)
(*  Cross-reference: the coercion-free literal style used here matches the   *)
(*  `Formula` constructors of Part_III.v one level up (`EqFormula` ↔ `Eq`,   *)
(*  `AndFormula` ↔ `And`, `ForallFormula` ↔ `Forall`, ...).                 *)
(*                                                                           *)
(* ========================================================================= *)

(* ============================ WORKED EXAMPLES ============================ *)
(*                                                                           *)
(*  Each `Example` below is a *checkable* Coq sentence: Coq type-checks the  *)
(*  displayed constructor application and adds the definition.  They double *)
(*  as the canonical "how do I build a formula?" recipes for this library.   *)
(*                                                                           *)
(*  Reading guide:  P_1(x, y) is rendered `Pred 1 [x; y]`.                   *)
(*                                                                           *)
(* ========================================================================= *)

(* Atomic formulas --------------------------------------------------------- *)

(* A predicate call:  P_1(2, 3). *)
Example predicate_example : Fo := Pred 1 [2; 3].

(* An atomic equality:  2 = 3. *)
Example equality_example : Fo := Eq 2 3.

(* Compound formulas ------------------------------------------------------- *)

(* Conjunction:  2 = 3 ∧ P_1(2, 3). *)
Example and_example : Fo := And (Eq 2 3) (Pred 1 [2; 3]).

(* Disjunction:  2 = 3 ∨ P_1(2, 3). *)
Example or_example : Fo := Or (Eq 2 3) (Pred 1 [2; 3]).

(* Implication:  2 = 3 ⇒ P_1(2, 3). *)
Example imp_example : Fo := Imp (Eq 2 3) (Pred 1 [2; 3]).

(* Negation:  ¬(2 = 3). *)
Example not_example : Fo := Not (Eq 2 3).

(* Quantified formulas ----------------------------------------------------- *)

(* Universal closure:  ∀1, (1 = 2). *)
Example forall_example : Fo := Forall 1 (Eq 1 2).

(* Existential assertion:  ∃1, (1 = 2). *)
Example exists_example : Fo := Exists 1 (Eq 1 2).

(* Nesting example:  ∀2, (2 = 3 ⇒ ∃1, P_1(1, 3)) — quantifiers scope over   *)
(* anything built from the constructors above, so formulas compose freely.  *)
Example nested_example : Fo :=
  Forall 2 (Imp (Eq 2 3) (Exists 1 (Pred 1 [1; 3]))).

(* ====================== A FIRST META-THEOREM (DEMO) ====================== *)
(*                                                                           *)
(*  This is the canonical pattern for reasoning about `Fo` in this library:  *)
(*  define a recursive (structural) function, then prove a property of it    *)
(*  by `induction f` — one case per constructor.                             *)
(*                                                                           *)
(*  `size f` counts the number of syntactic nodes of the formula `f`.        *)
(*  Atomic formulas (`Pred`, `Eq`) contribute exactly one node; each         *)
(*  connective or quantifier adds one and recurses on the subformula(s).     *)
(*                                                                           *)
(*  Related folklore: this is the measure against which induction on         *)
(*  subformulas is justified in every development of first-order logic       *)
(*  (mirrored structurally by the `Formula` hierarchy in `Part_III.v`).      *)
(*                                                                           *)
(* ========================================================================= *)

Fixpoint size (f : Fo) : nat :=
  match f with
  | Pred _ _      => 1
  | Eq _ _        => 1
  | And f1 f2     => S (size f1 + size f2)
  | Or f1 f2      => S (size f1 + size f2)
  | Imp f1 f2     => S (size f1 + size f2)
  | Not f         => S (size f)
  | Forall _ f    => S (size f)
  | Exists _ f    => S (size f)
  end.

(* `size` is always positive: atomic formulas already have one node and     *)
(* each composite constructor stores at least one subformula under an       *)
(* explicit successor.  Proof: induction on `f`; every one of the eight     *)
(* cases reduces to positivity of an immediate successor (`le_n_S`, then    *)
(* the trivial `0 <= _`).                                                   *)
Lemma size_ge_one : forall f : Fo, 1 <= size f.
Proof.
  intro f; induction f; simpl; solve
    [ reflexivity
    | apply le_n_S; apply Nat.le_0_l ].
Qed.

(* Example application of the lemma together with its defining function.    *)
(* The composite example `and_example` has exactly three nodes:             *)
(*   `And` + node of `Eq 2 3` + node of `Pred 1 [2; 3]`.                    *)
Example size_of_and_example : size and_example = 3.
Proof. reflexivity. Qed.

(* The lemma applies to every concrete formula, e.g.: *)
Example size_ge_one_and_example : 1 <= size and_example := size_ge_one _.

End Part_III.

(* ============================ POSSIBLE EXTENSIONS ======================== *)
(*                                                                           *)
(*  Natural follow-ups for later tickets (kept out of scope for Ticket 001): *)
(*   - `free_vars : Fo -> list nat` and a capture-avoiding substitution      *)
(*     `subst : nat -> nat -> Fo -> Fo`, gated by freshness lemmas.          *)
(*   - A translation `Fo -> Formula` into the Hilbert-style syntax of        *)
(*     `Part_III.v`, so the deduction system there can be applied to these   *)
(*     example terms directly.                                              *)
(*   - Decidability facts: `eq_fo : Fo -> Fo -> bool` (structural equality   *)
(*     decider) and a `size`-based termination guard for future             *)
(*     normalization functions.                                             *)
(*                                                                           *)
(*  When extending this file, keep EVERY new definition inside              *)
(*  `Section Part_III ... End Part_III.` so the `make check` build stays     *)
(*  aligned with `.gitlab-ci.yml`.                                          *)
(*                                                                           *)
(* =========================== END OF ROADMAP ============================== *)
