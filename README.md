# Jech Library Documentation

This library contains formalizations of key set theory concepts and first-order logic.

## Key Definitions and Theorems

### Axiom of Infinity (axInfty)

The Axiom of Infinity states that there exists a set (omega) that is inductive and contains the empty set. An inductive set is a set that contains the empty set and is closed under the successor operation. The Axiom of Infinity ensures the existence of such a set, which is often referred to as the set of natural numbers.

#### Example

```python
from jech import axInfty

# Define the Axiom of Infinity
omega = axInfty()

# Verify the Axiom of Infinity
assert omega.is_inductive()
assert omega.contains_empty_set()
```

#### Usage Instructions

1. Import the `axInfty` function from the `jech` module.
2. Call the `axInfty` function to obtain the set omega.
3. Verify that omega is inductive and contains the empty set using the provided assertions.

### First-Order Logic Syntax

#### Variables

Variables are fundamental components in first-order logic. They are used to represent elements of sets and are typically denoted by lowercase letters such as x, y, and z. In the Jech library, variables are defined as strings.

#### Example

```python
from jech import Variable

# Define a variable
x = Variable('x')

# Verify the variable
assert x.name == 'x'
```

#### Usage Instructions

1. Import the `Variable` class from the `jech` module.
2. Create a variable by instantiating the `Variable` class with a string representing the variable name.
3. Verify the variable by accessing its `name` attribute.

#### Terms

Terms are expressions that represent elements of a domain. In first-order logic, terms can be either variable terms or function terms. Variable terms are simply variables, while function terms are formed by applying a function symbol to a list of terms.

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

#### Usage Instructions

1. Import the `VariableTerm` and `FunctionTerm` classes from the `jech` module.
2. Create a variable term by instantiating the `VariableTerm` class with a string representing the variable name.
3. Create a function term by instantiating the `FunctionTerm` class with a string representing the function symbol and a list of terms representing the arguments.
4. Verify the terms using the provided assertions.

#### Formulas

Formulas are logical expressions that can be either true or false. In first-order logic, formulas are built using logical connectives, quantifiers, and predicates. They are used to express statements about the elements of a domain.

#### Example

```python
from jech import Formula

# Define a formula
formula = Formula('P(x)')

# Verify the formula
assert formula.is_formula()
```

#### Usage Instructions

1. Import the `Formula` class from the `jech` module.
2. Create a formula by instantiating the `Formula` class with a string representing the logical expression.
3. Verify the formula using the provided assertion.

### First-Order Logic Axioms

The axioms of first-order logic provide the foundational rules for logical reasoning. They include the axioms of equality, implication, conjunction, disjunction, negation, and universal quantification. These axioms are essential for deriving logical consequences and proving theorems.

#### Example

```python
from jech import Axiom

# Define an axiom
axiom = Axiom('equality')

# Verify the axiom
assert axiom.is_axiom()
```

#### Usage Instructions

1. Import the `Axiom` class from the `jech` module.
2. Create an axiom by instantiating the `Axiom` class with a string representing the type of axiom (e.g., 'equality', 'implication').
3. Verify the axiom using the provided assertion.

### First-Order Logic Inference Rules

The inference rules of first-order logic provide the mechanisms for deriving new formulas from existing ones. They include modus ponens, generalization, and introduction of logical connectives. These rules are essential for constructing proofs and logical arguments.

#### Example

```python
from jech import InferenceRule

# Define an inference rule
rule = InferenceRule('modus_ponens')

# Verify the inference rule
assert rule.is_inference_rule()
```

#### Usage Instructions

1. Import the `InferenceRule` class from the `jech` module.
2. Create an inference rule by instantiating the `InferenceRule` class with a string representing the type of inference rule (e.g., 'modus_ponens', 'generalization').
3. Verify the inference rule using the provided assertion.

## Conclusion

The Jech library provides a comprehensive formalization of key set theory concepts and first-order logic. It includes definitions for sets, functions, relations, and logical expressions, along with axioms and inference rules. The library is designed to support formal reasoning and theorem proving in mathematical logic.

To get started with the Jech library, import the necessary classes and functions from the `jech` module, create instances of the relevant objects, and use the provided methods to verify and manipulate these objects. The library's documentation provides detailed examples and usage instructions for each component.

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