# Jech Library Documentation

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
