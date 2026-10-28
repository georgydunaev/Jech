# Jech Library Documentation

## Overview

The Jech library is a Python library for working with first-order logic. It provides classes for representing formulas, models, and proofs.

## Installation

To install the Jech library, you can use pip:

```bash
pip install jech
```

## Usage

Here is an example of how to use the Jech library:

```python
from jech.first_order_logic import Formula, Model, Proof

# Create a formula
formula = Formula("∀x P(x) → P(a)")
print(f"Formula: {formula}")

# Create a model
model = Model()
print(f"Model: {model}")

# Create a proof
proof = Proof()
print(f"Proof: {proof}")
```

### Detailed Usage

#### Formula Class

The `Formula` class is used to represent a first-order logic formula. It takes a string representing the formula as an argument. The formula string can include logical operators, quantifiers, and predicates. For example, "∀x P(x) → P(a)" represents a formula stating that for all x, if P(x) is true, then P(a) is true.

#### Model Class

The `Model` class is used to represent a model for first-order logic. It can be used to evaluate formulas and construct proofs. The `Model` class is initialized without any arguments.

#### Proof Class

The `Proof` class is used to represent a proof in first-order logic. It supports proof construction and verification. The `Proof` class is initialized without any arguments.

Here is an example of how to use the Jech library:

```python
from jech.first_order_logic import Formula, Model, Proof

# Create a formula
formula = Formula("∀x P(x) → P(a)")
print(f"Formula: {formula}")

# Create a model
model = Model()
print(f"Model: {model}")

# Create a proof
proof = Proof()
print(f"Proof: {proof}")
```

## Main Components

1. **Formula**: Represents a logical formula. It can be created using the `Formula` class and supports various logical operations.
2. **Model**: Represents a model in first-order logic. The `Model` class provides methods for evaluating formulas and checking satisfiability.
3. **Proof**: Represents a proof in first-order logic. The `Proof` class supports proof construction and verification.

## Additional Usage

The Jech library can also be used to perform more complex operations, such as checking the validity of a formula or generating proofs. For more advanced usage, refer to the source code and inline comments.


Here is an example of how to use the Jech library:

```python
from jech.first_order_logic import Formula, Model, Proof

# Create a formula
formula = Formula("∀x P(x) → P(a)")
print(f"Formula: {formula}")

# Create a model
model = Model()
print(f"Model: {model}")

# Create a proof
proof = Proof()
print(f"Proof: {proof}")
```
