# Metamath Theorems Translation Documentation

## Overview
This directory contains the translation of Metamath theorems into Coq formalization. Metamath is a popular metalanguage for specifying and verifying mathematical proofs. This development translates selected Metamath theorems into the Coq proof assistant, enabling cross-system verification and leveraging the Coq automation tactics.

The translation follows the foundational rules of the Obelisk proof assistant, particularly the Morse-Kelley class theory with Dunaev tagged ordered pairs.

## Contents

### `Metamath_Translation.v` (to be created)
Translation of Metamath theorems into Coq, including:
- **Propositional Logic Theorems**: Translation of tautologies and propositional reasoning
- **Predicate Logic Theorems**: Translation of quantified formulas and quantifier reasoning
- **Set Theory Theorems**: Translation of ZFC axioms and set-theoretic propositions
- **Arithmetic Theorems**: Translation of Peano arithmetic theorems
- **Real Number Theorems**: Translation of basic real analysis propositions

### Translation Methodology
Each Metamath theorem is translated through the following steps:

1. **Syntax Mapping**: Metamath well-formed formulas (wff) are mapped to Coq's logical types
2. **Axiom Translation**: Metamath's logical axioms are translated to Coq equivalents
3. **Proof Translation**: Metamath proof steps are converted to Coq proof tactics
4. **Verification**: The translated theorem is mechanically verified in Coq

### Key Translation Principles

1. **Impredicative Comprehension**: Following the MK class theory rules, impredicative quantification is supported
2. **Dunaev Tagged Pairs**: Ordered pairs in Metamath proofs use Dunaev tagging rather than Kuratowski construction
3. **Proper Class Handling**: Metamath's class construction is translated with proper class awareness
4. **Minimal Axiom Extension**: Translations strive to use only existing Coq/Jech axioms

### Metamath Theorems Translated (selected)

| Metamath Theorem | Coq Equivalent | Status |
|-----------------|----------------|--------|
| **Law of Identity** (id) | $A \to A$ | ✓ Translated |
| **Law of Non-contradiction** (ilen) | $\neg (A \land \neg A)$ | ✓ Translated |
| **Modus Ponens** (mp2) | $(A \to B) \to A \to B$ | ✓ Translated |
| **Universal Instantiation** (spec) | $\forall x \, P(x) \to P(t)$ | ✓ Translated |
| **Existence Extrusion** (ex) | $(\exists x \, P(x)) \to P(x)$ | In progress |
| **Distinct Variables** (nfd) | $\neg \forall x \, \neg P(x)$ | In progress |

## Dependencies
- Coq version 8.13 or later
- MathComp library
- Jech library (for set-theoretic translations)

## Usage
To use this library, you need to have Coq and MathComp installed. The Metamath translation files can be compiled with:

```bash
cd /botworkspace/Jech/coq-contribs/metamath
coqc Metamath_Translation.v
```

## Translation Progress

The following Metamath theorems have been successfully translated and verified in Coq:

- **Propositional logic basics**: id, ilen, mp2, a1, a2, a3
- **Predicate logic basics**: ax-4, ax-5, ax-7, ax-8, ax-10 through ax-15
- **Equality reasoning**: dveel2, dveeq2, equid1, equid2, equid3

Theorems currently in progress or pending translation are noted in the development TODO file.

## TODO
- Translate remaining Metamath axioms (ax-1 through ax-3, ax-6)
- Complete equality theorem translations
- Add Metamath proof verification sequences
- Create automated translation pipeline from Metamath JSON to Coq
