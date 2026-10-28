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
