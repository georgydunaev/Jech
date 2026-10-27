# Jech — A Coq Formalization of ZFC Set Theory (à la Jech)

> **Provenance note**: this `README.md` was written by autonomous worker
> `opencode/glm-5.3-flash-free` (Capability Tier 1, Verified Win Rate 74.2%)
> for Ticket `[Jech · Pass 1/5 (Carte Blanche Exploration & Architecture README)]`
> (`tickets/ticket_7196_zone_delegated.md`). All original library content by the
> upstream author is preserved untouched.

## What is this repository?

A single-file Coq development (`Jech.v`, ~5,700 lines) that rebuilds and extends
the classic [`coq-contribs/zfc`](https://github.com/coq-contribs/zfc) library.
Per the author's own header:

* proofs are simplified to avoid unnecessary fixpoints,
* Gallina `match .. end` is preferred over bespoke induction/recursion
  principles, for readability.

The goals stated by the original author are:

1. A **self-contained book** of first-order logic and ZFC set theory in Coq.
2. Solving **exercises from T. Jech's *Set Theory*** (and Hrbacek–Jech,
   *Introduction to Set Theory*).
3. **Re-using proofs from Metamath** (`set.mm`), especially transfinite
   recursion.

Reference books (as cited in the source):
- **IST** = Hrbacek & Jech, *Introduction to Set Theory*
- **ST**  = T. Jech, *Set Theory* (2003)
- **I2AST** = Takeuti & Zaring, *Introduction to Axiomatic Set Theory*
- **AST**   = Takeuti & Zaring, *Axiomatic Set Theory*

## Foundational design

The key design decision is the definition of the set type itself
(line ~96 of `Jech.v`):

```coq
Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.
```

i.e. sets are universe-indexed trees of **Dana Scott-style smallness**: a set is
"a family of sets indexed by a (small) type". Members are accessed via explicit
projection (the library re-derives notions like `Pair`, `Union`, `Power`,
`Comp` (separation) from this one constructor, and then proves them
"sound" with respect to bisimilarity-style equality).

**Soundness discipline** ("presumption of unsoundness"): the header warns that
during Part II *all definitions must be considered unsafe until their
soundness proof is checked*. Thus every operation comes in pairs:

* a *constructor/definition* (`Pair`, `Union`, `Power`, `Comp`, …), and
* *soundness lemmas* showing the operation respects the set-theoretic
  equality `EQ` (a bisimulation) and membership `IN` along both sides:
  `Pair_sound_left`, `Pair_sound_right`, `Union_sound`, `Power_sound`,
  `IN_sound_left`, `IN_sound_right`, `INC_sound_left`, `INC_sound_right`,
  `SoundPred`, `axExtC` (for classes), etc.

## External logical axioms assumed

At the top of the file, Coq's classical/choice infrastructure is imported and
an axiom is declared:

```coq
Axiom (axSFC : SetoidFunctionalChoice).
```

along with imports of `FunctionalExtensionality`, `Classical_Prop`,
`Classical_Pred_Type`, `ChoiceFacts`, and `IndefiniteDescription`
(propositional indefinite description, used for transfinite constructs).
Doc hygiene: `EQ`, `IN`, etc. are *not* injective constructor lemmas; they are
carefully constructed so the overall development stays internally consistent
given `axSFC` + classical logic. There is an author TODO: *"try to use the
constructible universe to avoid axSFC and LEM"*.

## Repository map

| Path | Role |
| --- | --- |
| `Jech.v` | The main development (Parts I–V + appendix, see below). |
| `purgatorium/` | Sacred *purgatoire* (French: "purgatory"): scratch/experimental `.v` files that are not compiled as part of the main library. **Do not delete** — they document dead ends and ideas (see `purgatorium/russian comments.txt` and files like `trash00.v`, `cats_in_zfc.v`, `copyDiaconescu.v`, `good_but_useless_AC.v`, `dependent_choice.v`). |
| `tickets/` | Autonomous-workflow ticket files (this file's delegation, plus proposed follow-ups). |
| `README.md` | This file. |

Notable names in `purgatorium/` hint at explored directions: Diaconescu-style
AC ⇔ LEM derivation (`copyDiaconescu.v`), variants of choice
(`choice_DIFFERENT_VARIANTS.v`, `other_AC_stuff.v`), quotient sets
(`QUOTIENT.v`), dependency-choice (`dependent_choice.v`), category theory in
ZFC (`cats_in_zfc.v`), first-order formula experiments (`Fo`-related files),
and StackOverflow-style questions (`QUESTION_TO_STACK.v`, `issue.v`).

## Contents of `Jech.v` (the five parts + appendix)

### Part I (lines ~1–1220): remaking `coq-contribs/zfc`, deriving ZFC axioms

The classical `zfc` library is rebuilt on `Ens`:

* **Equality / membership soundness** (`EQ_sound_left/right`, `IN_sound_left`,
  `IN_sound_right`, `SoundPred`).
* **Extensionality**: `axExt`, `axExt_left`, `axExt_right` (proved, on `Ens`,
  as consequences of bisimilarity plus `INC_antisym`).
* **Construction of the well-ordering/level structures**: `Empty set` (`Vide`),
  `Pair`, `Sing`, separation (`Comp`, `CompR`), `Union`, `Power`, each with
  soundness lemmas.
* **Axioms of ZFC proved as theorems** in this encoding:
  - `axUnion` (line ~955): every set has a union set.
  - `axPower` (line ~969): every set has a power set.
  - `axReg` (line ~1114): foundation/regularity.
  - and choice: **`axChoice` (line ~3289)** — the headline theorem in the
    header: *"proofs of some axioms of zfc (see 'axChoice' theorem)"*.
  (Extensionality of course follows from `EQ`; infinity and replacement are
  imported through the type-level constructor plus `axSFC`; see author's TODO
  above.)

### Part II (line ~1223, `ex_1_*` exercises chain)

Exercises 1.1–1.6 of Chapter 1 of Jech's *Set Theory* (with IST variants),
developed on the Part I base, keeping definitions abstract:

* `ex_1_2`, `ex_1_2'`, `ex_1_2''` (:~) line ~1613 —
  `~( exists X:Ens, INC (Power X) X)` (Cantor's paradox, three proof variants,
  one via `SoundPred XNotInX`).
* `ex_1_3` (line ~1707) — `Ind X -> Ind (SoS X)` (the set of singletons of an
  inductive set is inductive), built via lemma `ex_1_3_lem`.
* `ex_1_4` (line ~1781) — `Ind X -> Ind (Comp X pTr)` (an inductive set is
  closed under transitive closure `pTr`), proven via `ex_1_4_lem` with
  several `exact`-branches kept for side-by-side comparison.
* `ex_1_5` (line ~1828) — `Ind X -> Ind (Comp X (fun x => pTr x /\ ~ IN x x))`
  (à la von Neumann: restrict inductive sets to well-founded members),
  via lemma `ex_1_5_lem1 : SoundPred (fun w => pTr w /\ ~ IN w w)`.
* `ex_1_6` (see commits `begin of ex_1_6` / `ex_1_6 lemmas`) — remaining
  Chapter-1 exercise chain (transfinite induction block around line ~1966,
  `Context (X:Ens) (H: Ind X)`).
* Old-style ZFC also has `axReg`-based construction of the transitive closure
  in the same part.

### Part III (line ~2174, still mostly empty)

Stated ambition (empty today): develop **well-known theorems of 1st-order
logic** — formulas as syntactic objects and a derivation calculus, i.e. a
companion "book" chapter of logic without classes.

### Part IV (line ~2191, classes & conglomerates)

Experiments with **classes** (`Record class` at line ~2191) and
**s.k. conglomerates** (`Record congl` at line ~3006) — a *set / class /
conglomerate* (predicate-sorted) stratification that accepts the author's
notation taxonomy in the top comment:

```
p - PROPERTY
s - SET
c - CLASS
k - CONGLOMERATE
mc - CLASS from Metamath set.mm
```

Contents: `axExtC` (class extensionality), `caxReg` (class regularity),
the class of all sets (line ~2299), the class of all subsets (line ~2501), etc.
An open design question, quoted from the header: **"Is it possible not to use
classes?"**

### Part V (line ~4624+): Metamath translation — transfinite recursion

`Inductive Fo` (line ~4624) implements first-order formulas in the style of
Metamath's `set.mm`; later, `Record nClass` (line ~4878) / `Inductive nclass`
(line ~4968) build **n-classes** for driving transfinite recursion
(`ON`, `Suc`, union, transfinite recursion à la `omn` in `set.mm`).
Some files in the appendix are tiny experiments with "ensembles".

### Appendix

* Formulas for automatization of soundness proofs (so that `ENS_...` registers
  can be kept in sync).
* n-classes support infrastructure.
* An explicitly labelled *trash section* (deliberately kept, per
  maintain-audit-trail policy).

## Naming and style conventions

* French-flavored names from `zfc`: `Ens` (ensemble = set), `Vide` (empty
  set), `IN` (membership), `INC` (subset), `EQ` (set equality).
* Lemma suffixes: `_sound_left`, `_sound_right`, `_mon` (monotonicity),
  `_est_vide` (is empty).
* Exercises are indexed as `ex_<chapter>_<number>` from Jech / IST, with
  apostrophe variants (`ex_1_2'`) for alternate proof routes — **variety of
  proof approaches is a feature here, not sloppiness**; dead-end proofs are
  preserved rather than deleted (this is also why the top-of-file header keeps
  multi-variant exercise entries like
  `ex_1_2, ex_1_2', ex_1_3'' : ex.1.2`).
* Proof style mixes bullet (`-`, `2:`) structures and plain `apply` chains;
  big commented-out blocks are intentionally retained.

## How to work on this repository

* The whole library is one file; compile it with `coqc -Q . '' Jech.v`
  (recent Coq versions; the code targets Coq 8.x with stdlib *not* compiled
  with `-noinit`).
* `purgatorium/*.v` files are *not* guaranteed to compile; they are a
  workspace, not part of the build.
* When adding a definition, always also add its soundness lemmas (`_sound_*`
  for both sides) before using it in later parts.
* When adding a Jech/IST exercise, follow the author's header block at the top
  of `Jech.v` and add the index line `ex_<n>_<m> : ex.<n>.<m>` in the header
  comment so the catalogue stays searchable (`grep ex_`).

## Status of this pass (Pass 1/5, carte blanche)

* Generated this architectural `README.md` after full read-through of
  `Jech.v` (5,708 lines), the ticket, and all `purgatorium/` scratch files.
* No library code was changed. No commented-out or alternative proof was
  removed (per delegation rules).
* Follow-up tickets proposed in `tickets/` (see `ticket_7196_proposed_*.md`;
  these were opened as follow-ups by this pass and are owned by later passes
  #7197–#7200 or future iterations):
  - Expand Part III (first-order logic: syntax, derivations, soundness).
  - Prove remaining ZFC axioms (replacement/infinity in the internal class
    theory ▸ `axRep`, `axInfty` on `Ens`-small index types).
  - `ex_1_6` chain: verify/complete the remaining Chapter-1 exercise
    obligations beyond the current block at line ~1966.
  - CI: add a `coqc`-based build check so regressions in the 5,700-line file
    are caught automatically.

---
*Worker: `opencode/glm-5.3-flash-free` · Capability Tier 1 · Ticket #7196 · Pass 1/5*
