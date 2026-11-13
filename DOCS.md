# Jech Library Documentation

This library contains formalizations of key set theory concepts and first-order logic,
with both Coq (for machine-checked proofs) and Python (for prototyping and everyday use).

The name "Jech" references Jerzy Jech's work on set theory, particularly his development
of Scott-style `Ens` (set-theoretic) constructions and his comprehensive treatment of ZFC axioms.

## Overview

The Jech library consists of two main components:

1. **Coq Development** (`Jech.v`, `Part_III.v`): Machine-checked formal proofs of set theory axioms
   and first-order logic derivations. In `Part_III.v`, structural inference rules (Modus Ponens,
   Generalization) and propositional axioms have machine-checked semantic soundness under `Sat`,
   with quantifier substitution semantics explicitly hypothesized. This provides a rigorous ground-truth layer.

2. **Python Bindings** (`main.py`, `setup.py`): Higher-level interfaces for working with the
   concepts defined in Coq, including `Formula`, `Model`, `Proof` classes and implementations
   of key ZFC axioms.

The core innovation of this library is the use of the `sup` constructor (Scott's sup-delta
construction) to internally prove axioms like **Axiom of Infinity** and **Axiom of Replacement**
without postulating them, leveraging impredicative comprehension over Scott-setrees.

## Key Definitions and Theorems

### Axiom of Infinity (axInfty)

**Statement**: The Axiom of Infinity states that there exists a set which contains the empty set
and is closed under the operation of taking the successor set. In this library, the set of
natural numbers `ω` is *constructed* rather than postulated, using the `sup` constructor:

```coq
Theorem axInfty : exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n)).
```

The constructed set `Y := sup Nat (fun n => Nat n)` contains exactly the tagged natural numbers
as members — the analogue of `ω` in Jech Chapter 1.

**Key components**:
- `Ens` — the impredicative universe of sets-as-sup-trees
- `sup : forall A : Type, (A -> Ens) -> Ens` — supremum constructor
- `Nat` — tagged constructor for natural-number atoms
- `EQ` / `IN` — extensional equality and membership

**Python usage**:

```python
from jech import axInfty

# Define the Axiom of Infinity
omega = axInfty()

# Verify the Axiom of Infinity
assert omega.is_inductive()
assert omega.contains_empty_set()
```

**Coq example** (see `Jech.v`, axInfty walkthrough section):

```coq
Theorem axInfty : exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n)).
Proof.
  exists (sup Nat (fun n:Nat => Nat n)).
  intro z; split; intro H.
  + apply IN_sup.
    exact H.
  + destruct H as [n fxz].
    eapply IN_sup.
      exact (Nat n).
      exact fxz.
Qed.
```

### Axiom of Replacement (axRep)

**Statement**: The Axiom of Replacement states that if for every element `x` in a set `A`
there is a unique element `y` in a set `B` such that a relation `R(x, y)` holds,
then there exists a set `C` such that for every `y` in `C`, there exists an `x` in `A`
such that `R(x, y)`. Like `axInfty`, this is internally constructed using the `sup`
constructor.

**Coq reference** (see `src/axioms/axRep.ML` and `src/proofs/axRep_axInfty.ML`):

The proof constructs the image of a set under a functional class using the `sup`
constructor and verifies that the resulting set contains exactly the function values.

**Python usage**:

```python
from jech import axRep

# Define replacement for a function f: A -> B
C = axRep(A, f)

# Verify that for every x in A, f(x) is in C
assert forall_x_in_A_implies_fx_in_C
```

### First-Order Logic Syntax

The library provides an inductive type `Fo` for first-order formulas with the following
constructors:

| Constructor | Meaning | Example |
|---|---|---|
| `Pred n args` | Atomic predicate | `Pred 1 [2; 3]` |
| `Eq t1 t2` | Atomic equality | `Eq 2 3` |
| `And f1 f2` | Conjunction | `And (Eq 2 3) f` |
| `Or f1 f2` | Disjunction | `Or (Eq 2 3) f` |
| `Imp f1 f2` | Implication | `Imp (Eq 2 3) f` |
| `Not f` | Negation | `Not (Eq 2 3)` |
| `Forall x f` | Universal quantification | `Forall 1 (Eq 1 2)` |
| `Exists x f` | Existential quantification | `Exists 1 (Eq 1 2)` |

**Coq examples** (see `Jech.v`):

```coq
Example predicate_example : Fo := Pred 1 [2; 3].
Example equality_example : Fo := Eq 2 3.
Example and_example : Fo := And (Eq 2 3) (Pred 1 [2; 3]).
Example or_example : Fo := Or (Eq 2 3) (Pred 1 [2; 3]).
Example imp_example : Fo := Imp (Eq 2 3) (Pred 1 [2; 3]).
Example not_example : Fo := Not (Eq 2 3).
Example forall_example : Fo := Forall 1 (Eq 1 2).
Example exists_example : Fo := Exists 1 (Eq 1 2).
Example nested_example : Fo :=
  Forall 2 (Imp (Eq 2 3) (Exists 1 (Pred 1 [1; 3]))).
```

**Python usage** (see `main.py`):

```python
from jech.first_order_logic import Formula, Model, Proof

# Create a formula
formula = Formula("∀x P(x) -> P(a)")
print("Formula:", formula)

# Create a model
model = Model(["a", "b"], ["P"], {"P": ["a", "b"]})
print("Model:", model)

# Create a proof
proof = Proof([Formula("P(a)"), Formula("P(b)")], Formula("∀x P(x)"), [Formula("P(a)"), Formula("P(b)"), Formula("∀x P(x)")])
print("Proof:", proof)
```

### Hilbert-Style Derivation Calculus (Part_III.v)

The `Part_III.v` file defines a richer `Formula` type with distinct `Var`/`Term` sorts
and explicit `True`/`False` cases, used by the Hilbert-style derivation calculus. This
includes:

- **Axioms** (Haxiom1-Haxiom8): Propositional, equality, and quantification axioms
- **Inference rules** (AxiomProof, MP, Gen): Modus ponens and generalization
- **Semantic Soundness** (`Theorem soundness`): Inductive proof without admit showing that every provable formula is satisfied under all variable assignments `Sat e F`.

## Python API

### `Formula`

Represents a first-order logic formula constructed from string input or Coq-style constructors.

- `__init__(formula_str)`: Initialize from a string like `"∀x P(x) -> P(a)"`
- `is_formula()`: Verify the object is a valid formula
- `evaluate(model)`: Evaluate the formula in a given model

### `Model`

Represents a first-order logic model for evaluation.

- `__init__(constants, predicates, assignments)`: Create a model
  - `constants`: List of constant symbols
  - `predicates`: List of predicate names
  - `assignments`: Dict mapping predicate names to lists of constant tuples

- `evaluate(formula)`: Evaluate a formula in the model and return boolean result

### `Proof`

Represents a proof in the Hilbert-style calculus.

- `__init__(axioms, conclusion, steps)`: Create a proof
  - `axioms`: List of axiom formulas
  - `conclusion`: The conclusion formula
  - `steps`: List of proof step formulas

- `is_valid()`: Check if the proof is valid
- `print_proof()`: Display the proof structure

## Functions

The Jech library provides the following functions:

| Function | Description |
|---|---|
| `parse_formula(formula_str)` | Parse a string into a `Formula` object |
| `evaluate_formula(formula, model)` | Evaluate a formula in a model |
| `prove_theorem(axioms, theorem, steps)` | Construct a proof for a theorem |
| `axInfty()` | Construct and return the set ω (Axiom of Infinity) |
| `axRep(A, f)` | Construct the replacement set for function `f` over `A` |

## Examples Directory

The `examples/` directory contains standalone Coq example files demonstrating various features:

- `example_1.v`: Basic set operations (`{1, 2, 3}`)
- `example_2.v`: Set operations without compilation
- `example_3.v`: ZFC axioms and theorems (extensionality, pairing, intersection, difference)
- `example_4.v`: Advanced concepts (Infinity, Power Set, Replacement)
- `example_5.v`: Complex set operations (union, intersection, difference, predicate-based sets)

**To add new examples**, copy the pattern of existing files and place them in `examples/`.
They are informal sketches and are not part of the CI build (which runs on `Jech.v` only).

## Getting Started

### With Coq

```bash
coqc -Q . '' Jech.v
```

### With Python

```bash
pip install -e .
from jech import axInfty, Variable, VariableTerm, Formula, Axiom, InferenceRule

# Axiom of Infinity
omega = axInfty()
assert omega.is_inductive()
assert omega.contains_empty_set()

# Variables and terms
x = Variable('x')
x_term = VariableTerm('x')
assert x.name == 'x'
assert x_term.is_variable_term()

# Formulas
formula = Formula('P(x)')
assert formula.is_formula()

# Axioms and inference rules
axiom = Axiom('equality')
assert axiom.is_axiom()
rule = InferenceRule('modus_ponens')
assert rule.is_inference_rule()
```

### Full Integration

```python
from jech.first_order_logic import Formula, Model, Proof

# Define a formula
formula = Formula("∀x P(x) -> P(a)")

# Define a model
model = Model(["a", "b"], ["P"], {"P": ["a", "b"]})

# Evaluate the formula in the model
result = model.evaluate(formula)
print("Formula evaluates to:", result)

# Construct a proof
proof = Proof(
    axioms=[Formula("P(a)")],
    conclusion=Formula("∀x P(x)"),
    steps=[Formula("P(a)"), Formula("∀x P(x)")]
)
print("Proof constructed:", proof.is_valid())
```

## License

This library is licensed under the MIT License. See `LICENSE` or the `LICENSE` file in the root directory for details.