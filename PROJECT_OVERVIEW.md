# Project Overview: Mechanized Axiomatic Set Theory after Thomas Jech (`Jech`)

## 1. Purpose and Scope
`Jech` (`/botworkspace/Jech`) formalizes axiomatic set theory following Thomas Jech's *Set Theory* (3rd Millennium Edition) across Coq (`Jech.v`, `Part_III.v`, `section_choice.v`, `section_cumulative_hierarchy.v`, `section_mostowski.v`) and an accompanying Python verification library (`jech/`). Compiled `.vo` files are strictly immutable per Fact 11.

## 2. Architecture and Key Files
- **Coq Set Theory Formalizations**:
  - [Jech.v](file:///botworkspace/Jech/Jech.v) — Core ZFC axioms (Extensionality, Pairing, Comprehension, Union, Power Set, Infinity, Replacement, Foundation), ordered pairs, relations, functions, ordinals, and inductive sets.
  - [section_choice.v](file:///botworkspace/Jech/section_choice.v) — Axiom of Choice, Zorn's Lemma, Teichmueller-Tukey Lemma, and Well-Ordering Theorem equivalences.
  - [section_cumulative_hierarchy.v](file:///botworkspace/Jech/section_cumulative_hierarchy.v) — Von Neumann cumulative hierarchy stages $V_\alpha$, rank function, and regularity properties.
  - [section_mostowski.v](file:///botworkspace/Jech/section_mostowski.v) — Extensional well-founded relations and Mostowski transitive collapse.
  - [Part_III.v](file:///botworkspace/Jech/Part_III.v) — Advanced cardinal, cofinality, and forcing preliminaries.
- **Python Reference Library (`jech/` and `tests/`)**:
  - Finite hereditary set models, ordinal/cardinal arithmetic verifiers, and structural unit tests.
- [DOCS.md](file:///botworkspace/Jech/DOCS.md) and [README.md](file:///botworkspace/Jech/README.md) — Detailed theorem documentation.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/Jech/tests -p "test_*.py"
```
