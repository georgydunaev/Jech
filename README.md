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

## Getting Started

To use this library, you can import the required modules and apply the definitions and theorems in your proofs.

### Example

```python
from jech import axInfty, Variable, VariableTerm, Formula, Axiom, InferenceRule

# Define the Axiom of Infinity
omega = axInfty()

# Define a variable
x = Variable('x')

# Define a variable term
x_term = VariableTerm('x')

# Define a formula
formula = Formula('P(x)')

# Define an axiom
axiom = Axiom('equality')

# Define an inference rule
rule = InferenceRule('modus_ponens')

# Verify the definitions and theorems
assert omega.is_inductive()
assert omega.contains_empty_set()
assert x.name == 'x'
assert x_term.is_variable_term()
assert formula.is_formula()
assert axiom.is_axiom()
assert rule.is_inference_rule()
```

## License

This library is licensed under the MIT License.