# Jech Library Documentation

This library contains formalizations of key set theory concepts and first-order logic.

## Key Definitions and Theorems

### Axiom of Infinity (axInfty)

The Axiom of Infinity states that there exists a set (omega) that is inductive and contains the empty set.

#### Example

```python
from jech import axInfty

# Define the Axiom of Infinity
omega = axInfty()

# Verify the Axiom of Infinity
assert omega.is_inductive()
assert omega.contains_empty_set()
```

### First-Order Logic Syntax

#### Variables

Variables are defined as strings.

#### Example

```python
from jech import Variable

# Define a variable
x = Variable('x')

# Verify the variable
assert x.name == 'x'
```

#### Terms

Terms are defined as either variable terms or function terms.

#### Example

```python
from jech import VariableTerm, FunctionTerm

# Define a variable term
x = VariableTerm('x')

# Define a function term
f = FunctionTerm('f', [x])

# Verify the terms
assert x.is_variable_term()
assert f.is_function_term()
```

#### Formulas

Formulas are defined as logical expressions.

#### Example

```python
from jech import Formula

# Define a formula
formula = Formula('P(x)')

# Verify the formula
assert formula.is_formula()
```

### First-Order Logic Axioms

The axioms of first-order logic include the axioms of equality, implication, conjunction, disjunction, negation, and universal quantification.

#### Example

```python
from jech import Axiom

# Define an axiom
axiom = Axiom('equality')

# Verify the axiom
assert axiom.is_axiom()
```

### First-Order Logic Inference Rules

The inference rules of first-order logic include modus ponens, generalization, and introduction of logical connectives.

#### Example

```python
from jech import InferenceRule

# Define an inference rule
rule = InferenceRule('modus_ponens')

# Verify the inference rule
assert rule.is_inference_rule()
```

## Overview

The Jech library is a Python library for working with first-order logic. It provides classes for representing formulas, models, and proofs in first-order logic.

## Classes

### Formula

The `Formula` class is used to represent a first-order logic formula. It takes a string representing the formula as an argument. The formula string can include logical operators, quantifiers, and predicates.

### Model

The `Model` class is used to represent a model in first-order logic. It takes a set of constants, a set of functions, and a set of relations as arguments.

### Proof

The `Proof` class is used to represent a proof in first-order logic. It takes a set of axioms, a set of inference rules, and a set of theorems as arguments.

## Functions

The Jech library provides several functions for working with first-order logic. These functions include:

- `parse_formula`: Parses a string representing a first-order logic formula and returns a `Formula` object.
- `evaluate_formula`: Evaluates a first-order logic formula in a given model and returns the result.
- `prove_theorem`: Proves a given theorem in first-order logic using a given set of axioms and inference rules.

## Examples

The Jech library includes several examples demonstrating the usage of the classes and functions. These examples can be found in the `examples` directory.

## Main Function

The `main` function in the `main.py` file demonstrates the usage of the `Formula`, `Model`, and `Proof` classes. It creates instances of these classes and prints them to the console.
