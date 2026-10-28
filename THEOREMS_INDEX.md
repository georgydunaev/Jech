# Jech Library Theorems Index

## Definitions

### Formula

- **Description**: Represents a first-order logic formula.
- **Usage**: `Formula(formula_str)`
- **Example**: See `main.py` for example usage and detailed comments.

### Model

- **Description**: Represents a first-order logic formula.
- **Usage**: `Formula(formula_str)`

### Model

- **Description**: Represents a model for first-order logic.
- **Usage**: `Model()`

### Proof

- **Description**: Represents a proof in first-order logic.
- **Usage**: `Proof()`

## Key Theorems

1. **Soundness Theorem**: Every theorem provable in the Jech library is true in all models. This means that if a formula is provable, it is also valid in all models.
2. **Completeness Theorem**: Every valid formula is provable in the Jech library. This means that if a formula is valid in all models, it can be proven using the library.

### Detailed Descriptions

#### Soundness Theorem

The Soundness Theorem ensures that the Jech library does not produce false theorems. It states that every theorem provable in the library is true in all models. This is a fundamental property of any logical system.

#### Completeness Theorem

The Completeness Theorem ensures that the Jech library can prove all valid formulas. It states that every valid formula is provable in the library. This is a more advanced property and is often used to show that a logical system is complete.

1. **Soundness Theorem**: Every theorem provable in the Jech library is true in all models.
2. **Completeness Theorem**: Every valid formula is provable in the Jech library.

## Functions

1. `Formula.__init__`: Initializes a new formula.
2. `Model.evaluate`: Evaluates a formula in the model.
3. `Proof.construct`: Constructs a proof for a given theorem.


- **Description**: Represents a proof in first-order logic.
- **Usage**: `Proof()`
