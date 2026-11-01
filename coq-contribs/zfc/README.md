# ZFC Library Documentation

## Overview
This directory contains the Coq formalization of the Zermelo-Fraenkel set theory with the Axiom of Choice (ZFC). The library includes definitions of basic set theory concepts and proofs of some axioms of ZFC.

## Contents

### `ZFC.v`
The main file containing basic set theory definitions (empty set, singleton, pair) and the formal statement of key ZFC axioms as Coq axioms.

### `axioms.v`
Definitions and formal axioms of ZFC:
- **Axiom of Extensionality**: Two sets are equal iff they have the same elements.
- **Axiom of Pairing**: For any two sets x, y, there exists a set z whose elements are exactly x and y.
- **Axiom of Union**: For any set A, there exists a set B whose elements are exactly the elements of the elements of A.
- **Axiom of Power Set**: For any set x, there exists a set y whose elements are exactly the subsets of x.
- **Axiom of Infinity**: There exists an inductive set containing the empty set and closed under the successor operation.
- **Axiom of Regularity**: Every non-empty set x has an element y that is disjoint from x.
- **Axiom of Choice**: For any non-empty set x, there exists a choice function y that selects an element from each set in x.

### `theorems.v`
Theorems derived from the ZFC axioms:
- **Empty set uniqueness**: The empty set is unique.
- **Union of two sets**: The union of two sets is a set.
- **Power set**: The power set of a set is a set.

## Dependencies
- Coq version 8.13 or later
- MathComp library

## Usage
To use this library, you need to have Coq and MathComp installed. You can then compile the `.v` files using the Coq compiler:

```bash
cd /botworkspace/Jech/coq-contribs/zfc
coqc ZFC.v axioms.v theorems.v
```

## Axioms Detailed

All axioms are stated in Coq's native logic using the `in` membership relation and `=` equality.

- **Extensionality**: `forall A B:Type, A = B <-> forall x, x in A <-> x in B`
- **Pairing**: `forall x y:Type, exists z, forall w, w in z <-> w = x \/ w = y`
- **Union**: `forall A:Type, exists B, forall x, x in B <-> exists y, x in y /\ y in A`
- **Power**: `forall x, exists y, forall z, z in y <-> forall w, w in z -> w in x`
- **Infinity**: `exists x, empty_set \in x /\ forall y, y \in x -> y \cup {y} \in x`
- **Regularity**: `forall x, ~(x = empty_set) -> exists y, y \in x /\ forall z, z \in x -> z \notin y`
- **Choice**: `forall x, ~(x = empty_set) -> exists y, forall z, z \in x -> exists w, w \in y /\ forall u, u \in w -> u \in z`

## Theorems Detailed

Theorems in `theorems.v` are mechanically proved from the axioms:

- `empty_set_unique`: The empty set is characterized by having no elements.
- `union_set`: The union of two sets is a set (constructed using the pairing axiom).
- `power_set`: The power set of a set is a set (constructed using the power axiom).
