# Jech Library

## Overview

This library is a remake and extension of the `zfc` library, with a focus on simplifying proofs and increasing readability. It covers various parts of set theory, including the ZFC axioms, exercises from Jech's "Set Theory" book, and experiments with classes and many theorems about them.

## Structure

The library is divided into several parts:

1. **Part I**: Large isolated part of the `/coq-contribs/zfc/` library and proofs of some axioms of ZFC.
2. **Part II**: Development of the classic ZFC theory with exercises from Jech's "Set Theory" and "Introduction to Set Theory" books.
3. **Part III**: Development of formulas and derivations for first-order logic.

This part of the library focuses on developing the formal structure of first-order logic, including:

1. **Syntax**: Definition of well-formed formulas (WFFs) and terms
2. **Semantics**: Interpretation of formulas in models
3. **Proof Theory**: Natural deduction and sequent calculus systems
4. **Completeness Theorem**: Proof of the completeness of first-order logic

Key definitions:
- `Formula`: A syntactically valid expression in first-order logic
- `Model`: A structure that interprets the non-logical symbols of a language
- `Proof`: A sequence of formulas that follows the rules of inference

Example derivation:
```
1. ∀x P(x) → P(a) (Universal instantiation)
2. ∀x P(x) (Premise)
3. P(a) (From 1 and 2, modus ponens)
```
4. **Part IV**: Experiments with classes and many theorems about them.
5. **Part V**: Translation of Metamath theorems.

## Goals

1. Create a self-contained book of first-order logic and ZFC set theory.
2. Solve exercises from Jech's "Set Theory".
3. Re-use proofs from Metamath.

## Key Definitions

- `p`: PROPERTY - A property is a collection of sets that share a common characteristic. Properties are used to define classes and other constructs in set theory.
- `s`: SET - A set is a collection of distinct objects, considered as an object in its own right. Sets are the fundamental building blocks of set theory.
- `c`: CLASS - A class is a collection of sets that is too large to be considered a set. Classes are used to avoid the paradoxes associated with the naive theory of sets.
- `k`: CONGLOMERATE - A conglomerate is a collection of classes. Conglomerates are used to extend the theory of classes to handle even larger collections.
- `mc`: CLASS from Metamath set.mm - A class defined in the Metamath set theory library, which provides a formalized foundation for set theory.

- `p`: PROPERTY
- `s`: SET
- `c`: CLASS
- `k`: CONGLOMERATE
- `mc`: CLASS from Metamath set.mm

## Theorems

### Part I: ZFC Axioms and Basic Definitions

1. **Axiom of Extensionality**: Two sets are equal if they have the same elements. This axiom ensures that the identity of a set is determined by its elements, not by any other property.
   - **Example**: If set A = {1, 2, 3} and set B = {1, 2, 3}, then A = B.

2. **Axiom of Pairing**: For any two sets, there exists a set that contains both of them. This axiom allows the formation of pairs of sets.
   - **Example**: For sets A and B, there exists a set C = {A, B}.

3. **Axiom of Union**: For any collection of sets, there exists a set that contains all the elements of the sets in the collection. This axiom allows the formation of the union of a collection of sets.
   - **Example**: For a collection of sets {A, B, C}, there exists a set D = A ∪ B ∪ C.

4. **Axiom of Power Set**: For any set, there exists a set that contains all the subsets of the original set. This axiom allows the formation of the power set of a set.
   - **Example**: For a set A = {1, 2}, the power set of A is {{}, {1}, {2}, {1, 2}}.

5. **Axiom of Infinity**: There exists a set that contains the empty set and is closed under the successor operation. This axiom ensures the existence of an infinite set.
   - **Example**: The set of natural numbers N = {0, 1, 2, ...} is an infinite set.

6. **Axiom of Regularity**: Every non-empty set contains an element that is disjoint from it. This axiom prevents the formation of sets that contain themselves as elements, which would lead to Russell's paradox.
   - **Example**: For a set A = {1, {2, 3}}, the element 1 is disjoint from A.

7. **Axiom of Choice**: For any collection of non-empty sets, there exists a function that selects one element from each set in the collection. This axiom is controversial and has implications in various areas of mathematics.
   - **Example**: For a collection of non-empty sets {A, B, C}, there exists a function f such that f(A) ∈ A, f(B) ∈ B, and f(C) ∈ C.

1. **Axiom of Extensionality**: Two sets are equal if they have the same elements.
2. **Axiom of Pairing**: For any two sets, there exists a set that contains both of them.
3. **Axiom of Union**: For any collection of sets, there exists a set that contains all the elements of the sets in the collection.
4. **Axiom of Power Set**: For any set, there exists a set that contains all the subsets of the original set.
5. **Axiom of Infinity**: There exists a set that contains the empty set and is closed under the successor operation.
6. **Axiom of Regularity**: Every non-empty set contains an element that is disjoint from it.
7. **Axiom of Choice**: For any collection of non-empty sets, there exists a function that selects one element from each set in the collection.

### Part II: Classic ZFC Theory

1. **Theorem 1.1**: The intersection of any two sets is a set. This theorem ensures that the intersection of two sets is also a set.
   - **Example**: For sets A = {1, 2, 3} and B = {2, 3, 4}, the intersection A ∩ B = {2, 3} is a set.

2. **Theorem 1.2**: The difference of any two sets is a set. This theorem ensures that the difference of two sets is also a set.
   - **Example**: For sets A = {1, 2, 3} and B = {2, 3, 4}, the difference A - B = {1} is a set.

3. **Theorem 1.3**: The Cartesian product of any two sets is a set. This theorem ensures that the Cartesian product of two sets is also a set.
   - **Example**: For sets A = {1, 2} and B = {3, 4}, the Cartesian product A × B = {(1, 3), (1, 4), (2, 3), (2, 4)} is a set.

4. **Theorem 1.4**: The power set of any set is a set. This theorem ensures that the power set of a set is also a set.
   - **Example**: For a set A = {1, 2}, the power set of A is {{}, {1}, {2}, {1, 2}}.

5. **Theorem 1.5**: The union of any collection of sets is a set. This theorem ensures that the union of a collection of sets is also a set.
   - **Example**: For a collection of sets {A, B, C}, the union A ∪ B ∪ C is a set.

1. **Theorem 1.1**: The intersection of any two sets is a set.
2. **Theorem 1.2**: The difference of any two sets is a set.
3. **Theorem 1.3**: The Cartesian product of any two sets is a set.
4. **Theorem 1.4**: The power set of any set is a set.
5. **Theorem 1.5**: The union of any collection of sets is a set.

### Part III: First-Order Logic

1. **Theorem 3.1**: The principle of explosion.
2. **Theorem 3.2**: The principle of identity.
3. **Theorem 3.3**: The principle of non-contradiction.
4. **Theorem 3.4**: The principle of excluded middle.

### Part IV: Classes and Conglomerates

1. **Theorem 4.1**: The class of all sets is a proper class.
2. **Theorem 4.2**: The class of all ordinals is a proper class.
3. **Theorem 4.3**: The class of all cardinals is a proper class.

### Part V: Metamath Theorems

1. **Theorem 5.1**: The axiom of extensionality in Metamath.
2. **Theorem 5.2**: The axiom of pairing in Metamath.
3. **Theorem 5.3**: The axiom of union in Metamath.
4. **Theorem 5.4**: The axiom of power set in Metamath.
5. **Theorem 5.5**: The axiom of infinity in Metamath.

## Requirements

- Coq 8.13 or later
- Docker (for CI)

## Local Compilation

To compile the `Jech.v` file locally, you can use the following command:
```bash
coqc -Q . '' Jech.v
```

## CI Setup

The `.gitlab-ci.yml` file is configured to run in GitLab CI using the `coqorg/coq` Docker image. To use this setup, you need to have GitLab CI configured in your project.

## Exercises

- `snis`
- `ex_1_2`, `ex_1_2'`, `ex_1_3''`: ex.1.2
- `ex_1_3`: ex.1.3
- `ex_1_4`: ex.1.4
- `ex_1_5`: ex.1.5
- `ex_1_6`: ex.1.6 (completed)


## Requirements
- Coq 8.13 or later
- Docker (for CI)

## Local Compilation
To compile the `Jech.v` file locally, you can use the following command:
```bash
coqc -Q . '' Jech.v
```

## CI Setup
The `.gitlab-ci.yml` file is configured to run in GitLab CI using the `coqorg/coq` Docker image. To use this setup, you need to have GitLab CI configured in your project.
