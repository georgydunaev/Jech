# Classes and Theorems Documentation

## Overview
This directory contains experiments with classes and many theorems about them in the Coq formalization of set theory. The development uses Morse-Kelley (MK) class theory with Dunaev tagged ordered pairs, as per the foundational rules of the Obelisk proof assistant.

## Contents

### `Classes.v` (to be created)
Definitions and basic properties of classes in Morse-Kelley set theory. This includes:
- The distinction between sets (elements of the universal class V) and proper classes (not in V)
- Class comprehension { x ∈ V | φ(x) } with impredicative quantification over all classes
- The empty class and universe class V
- Subclass relation and class equality
- Extensionality for classes

### `Class_Theorems.v` (to be created)
Many theorems about classes, including:
- **Class Extensionality**: Two classes are equal iff they have the same elements
- **Subclass Transitivity**: If A ⊆ B and B ⊆ C, then A ⊆ C
- **Empty Class Properties**: ∅ is a subclass of every class
- **Universal Class Properties**: V is a superclass of every class
- **Class Union and Intersection**: Operations on classes
- **Separation/Comprehension**: Subclass formation via class comprehension
- **Reflection Principles** for classes

## Foundational Rules (Morse-Kelley Class Theory)
Per the canonical foundational rules:

1. **Proper Classes as First-Class Entities**: 
   - $x \in V \iff \text{Set}(x)$ (A set is any class that is a member of another class)
   - $\text{Proper}(X) \iff \neg \text{Set}(X)$ (A proper class is not a member of any class)

2. **No Kuratowski Pairs for Proper Classes**:
   - NEVER define ordered pairs of proper classes using the Kuratowski construction
   - ALWAYS use Dunaev Tagged Ordered Pairs with fixed tags 1 and 2:
     $[A,B]_D = \operatorname{mark}(A,1) \cup \operatorname{mark}(B,2)$, where
     $\operatorname{mark}(X,k) = \{\langle u,k\rangle_K \mid u \in X\}$
   - The tags are constants, not a bound variable `tag`; projections satisfy
     $\operatorname{pr}_1([A,B]_D)=A$ and $\operatorname{pr}_2([A,B]_D)=B$ for arbitrary classes

3. **Full Impredicative Comprehension**:
   - In MK, class comprehension $\{ x \in V \mid \phi(x) \}$ permits formulas $\phi$ whose bound quantifiers range over **all classes**

## Dependencies
- Coq version 8.13 or later
- MathComp library
- Dunaev tagged ordered pairs implementation

## Usage
To use this library, you need to have Coq and MathComp installed. The class development follows the MK theory with Dunaev tagged pairs for proper class handling.

## Axioms and Theorems

### Basic Class Definitions
- **Set**: A class $x$ such that $x \in V$
- **Proper Class**: A class $X$ such that $\neg (X \in V)$
- **Class Extensionality**: $A = B \iff \forall x, x \in A \iff x \in B$

### Key Theorems (to be developed in `Class_Theorems.v`)
- Class extensionality theorem
- Subclass transitivity
- Empty class properties
- Universal class properties
- Comprehension principle
- Union and intersection of classes
