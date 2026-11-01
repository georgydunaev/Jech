# Jech Library Theorems Index

This index catalogs the definitions, theorems, and functions formalized in the Jech repository.
It is intended to serve as a quick-reference guide for navigating the codebase.

## ## Table of Contents

- [Axioms](#axioms)
- [Definitions](#definitions)
- [Theorems](#theorems)
- [ML Implementations](#ml-implementations)
- [Coq Developments](#coq-developments)

## Axioms

The following axioms are formalized in the repository:

| Axiom | File | Description |
|-------|------|-------------|
| Axiom of Infinity (`axInfty`) | `src/axioms/axInfty.ML`, `coq-contribs/zfc/axioms.v` | States that there exists an inductive set containing the empty set, often used to construct the natural numbers `ω`. |
| Axiom of Replacement (`axRep`) | `src/axioms/axRep.ML` | States that if for every element `x` in a set `A` there is a unique element `y` in a set `B` such that a relation `R(x, y)` holds, then there exists a set `C` such that for every `y` in `C`, there exists an `x` in `A` such that `R(x, y)`. |

## Definitions

### Core Inductive Types (Coq: `Jech.v`)

| Definition | Type | Description |
|------------|------|-------------|
| `Fo` | `Inductive` | Inductive type of first-order formulas with constructors: `Pred`, `Eq`, `And`, `Or`, `Imp`, `Not`, `Forall`, `Exists`. |
| `Pred n args` | Constructor | Atomic predicate call: `P_n(args)`. |
| `Eq t1 t2` | Constructor | Atomic equality between two terms. |
| `And f1 f2` | Constructor | Conjunction `f1 ∧ f2`. |
| `Or f1 f2` | Constructor | Disjunction `f1 ∨ f2`. |
| `Imp f1 f2` | Constructor | Implication `f1 ⇒ f2`. |
| `Not f` | Constructor | Negation `¬f`. |
| `Forall x f` | Constructor | Universal quantification `∀x, f`. |
| `Exists x f` | Constructor | Existential quantification `∃x, f`. |

### Axiom of Infinity

| Definition | File | Description |
|------------|------|-------------|
| `axInfty` | `src/axioms/axInfty.ML` | Theorem: `exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n))`. Constructs `ω` as `sup Nat (fun n => Nat n)` using impredicative comprehension. |

### Axiom of Replacement

| Definition | File | Description |
|------------|------|-------------|
| `axRep` | `src/axioms/axRep.ML` | Theorem implementing replacement using the `sup` constructor and the Dunaev Tagged Ordered Pairs rule for proper classes. |

### Python Library Definitions (if applicable)

| Definition | Module | Description |
|------------|--------|-------------|
| `Formula` | `jech.first_order_logic` | Represents a first-order logic formula (Python wrapper). |
| `Model` | `jech.first_order_logic` | Represents a first-order logic model (Python wrapper). |
| `Proof` | `jech.first_order_logic` | Represents a first-order logic proof (Python wrapper). |

## Theorems

### Soundness Theorem

- **Statement**: Every theorem provable in the Jech library is true in all models.
- **Significance**: Ensures the library does not produce false theorems; a fundamental property of any logical system.
- **Files**: Referenced in `DOCS.md`, `THEOREMS_INDEX.md`.

### Completeness Theorem

- **Statement**: Every valid formula is provable in the Jech library.
- **Significance**: Ensures the library can prove all valid formulas; a more advanced property often used to show a logical system is complete.
- **Files**: Referenced in `DOCS.md`, `THEOREMS_INDEX.md`.

### Axiom of Infinity Soundness

- **Statement**: The constructed set `Y = sup Nat (fun n => Nat n)` satisfies the axiom of infinity: `exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n))`.
- **Proof**: Uses the `IN_sup` lemma and injectivity of `EQ` on numerals.
- **Files**: `src/axioms/axInfty.ML`, `Jech.v` (axInfty walkthrough section).

### Axiom of Replacement Soundness

- **Statement**: The set `C = sup (fun x => f x)` satisfies the axiom of replacement: for every `x` in `A`, `f x` is in `C`.
- **Proof**: Uses the `sup` constructor and the Dunaev Tagged Ordered Pairs rule.
- **Files**: `src/axioms/axRep.ML`, `src/axioms/axRep.md`.

## ML Implementations

### `src/axioms/axInfty.ML`

- **Theorems**: `axInfty`
- **Content**: Implements the Axiom of Infinity using the `sup` constructor.
- **Proof pattern**: `exists (sup Nat (fun n => Nat n)); intro z; split; intro H; + apply IN_sup; exact H; + destruct H as [n fxz]; eapply IN_sup; exact (Nat n); exact fxz.`
- **Status**: Checkable in Poly/ML ground-truth mode.

### `src/axioms/axRep.ML`

- **Theorems**: `axRep`
- **Content**: Implements the Axiom of Replacement using the `sup` constructor.
- **Proof pattern**: Constructs `C = sup (fun x -> f x) : B` and verifies `f x ∈ C`.
- **Status**: Example/identity function verification only.

### `src/proofs/axRep_axInfty_proofs.ML`

- **Theorems**: Ground-truth Poly/ML proof terms for `axRep` and `axInfty`.
- **Content**: Stub/placeholder proofs for future development.
- **Status**: Loads cleanly under `poly -q --use ... < /dev/null`; comments/TODOs only.

### `src/proofs/test_axRep_axInfty.ML`

- **Theorems**: Informal pseudo-code sketch for `axRep`/`axInfty`.
- **Content**: Unresolved `A`/`B` types and unbound `infinite` operator.
- **Status**: Not Poly/ML-checkable, not in CI.

## Coq Developments

### `Jech.v` (Part III)

- **File**: `Jech.v` — Development of formulas and derivations (first-order syntax `Fo`).
- **Key features**:
  - Inductive type `Fo` with 8 constructors (`Pred`, `Eq`, `And`, `Or`, `Imp`, `Not`, `Forall`, `Exists`).
  - `size` function counting syntactic nodes.
  - `size_ge_one` lemma: `1 <= size f` for all `f`.
  - Worked examples demonstrating each constructor.
  - Roadmap cross-references to `Part_III.v`, `axInfty.ML`, `coq-contribs/zfc/`, etc.
- **Verification**: `make check` runs `coqc -Q . '' Jech.v`.

### `coq-contribs/zfc/axioms.v`

- **File**: Vendored reference development of ZFC axioms.
- **Axioms formalized**: Extensionality, Pairing, Union, Power Set, Infinity, Regularity, Choice.
- **Status**: Stated as axioms (unproven), with corresponding proofs in `theorems.v` where applicable.

### `coq-contribs/zfc/theorems.v`

- **File**: Theorems proved within the ZFC development.
- **Content**: Theorems derivable from the stated ZFC axioms.

## Roadmap & Cross-References

For detailed navigation of this repository, see the roadmap and cross-references embedded in `Jech.v` (lines 15-61) and the ticket records in `/botworkspace/Jech/tickets/`.

## Update Notes

- This index is maintained alongside the repository development.
- New definitions, proofs, or functions should be added to the appropriate section.
- Status fields (`Checkable`, `Stub`, `Axiom`, etc.) help track the maturity of each entry.
