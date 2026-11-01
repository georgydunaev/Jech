# Axiom of Infinity (axInfty)

The Axiom of Infinity states that there exists a set which contains the empty set and is closed under the operation of taking the successor set. In this library, the set of natural numbers `ω` is *constructed* rather than postulated, using the `sup` constructor (Scott's sup-delta construction) with impredicative comprehension.

## Statement

**Formal**: `exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n))`

**Informal**: The set `Y := sup Nat (fun n => Nat n)` contains exactly the tagged natural numbers as members — the analogue of `ω` in Jech Chapter 1.

## Key Components

- **`Ens`**: the impredicative universe of sets-as-sup-trees
- **`sup`**: supremum constructor, `sup : forall A : Type, (A -> Ens) -> Ens`, packs an index type `A` together with a family `f : A -> Ens`
- **`Nat`**: tagged constructor for natural-number atoms; `Nat n` its embedding as a set. Tagging is what keeps numerals distinguishable from other sup-trees under extensional equality.
- **`EQ`/`IN`**: extensional equality and membership. By the prelude lemma `IN_sup`, `IN z (sup A f)` unfolds to `exists a : A, EQ z (f a)`.

## Proof Outline

The proof has two directions:

1. **`IN (Nat n) Y`**: Apply `IN_sup` with index `n`.
2. **`IN z Y`**: Destruct `z` as `[n fxz]`, then `eapply IN_sup` with `Nat n` and `fxz`.

The infinity of the constructed set follows from the injectivity of `EQ` on numerals: `EQ (Nat n) (Nat m) <-> n = m`, which is what makes `Y` infinite.

## Context & Comparison

- This approach constructs `ω` impredicatively using the `sup` constructor and impredicative comprehension.
- Contrast with the classical ZFC axiom of infinity, which *postulates* an inductive set as an axiom: `exists x, empty_set \in x /\ forall y, y \in x -> y \cup {y} \in x`.
- The Jech/Ens development does not postulate infinity; it derives the existence of a set with the desired properties from the structure of `Ens` itself.

## References

- `src/axioms/axInfty.ML` — the ML implementation with the Coq-style proof term
- `THEOREMS_INDEX.md` — high-level index entry
- `DOCS.md` — comprehensive documentation with examples
- `coq-contribs/zfc/axioms.v` — classical ZFC axiom of infinity for comparison