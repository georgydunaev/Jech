# [JECH] Ticket 7805 -- Well-Founded Extensional Relations, Ordinal Rank, and Mostowski Collapse

**Repository:** `Jech`
**Status:** `RESOLVED`
**Created:** `2026-11-13T23:55:00Z`
**Resolved:** `2026-11-14T00:02:00Z`
**Author:** Jech Set Theory Specialist

## Scope and Objectives
1. Formalize well-founded relations, well-founded induction, and extensional binary relations in Coq according to Jech Set Theory (Chapters 2 and 6).
2. Mechanize the transitive closure TC(x) of relations and elements, establishing transitivity, step inclusion, and preservation of well-foundedness.
3. Mechanize the inductive ordinal rank function:
   rank(x) = sup { rank(y) + 1 | y E x }
   and prove strict monotonicity along E.
4. Formalize the Mostowski Collapsing Theorem:
   For any well-founded and extensional structure (A, E), construct the canonical collapse map pi to hereditary sets MSet:
   pi(x) = { pi(y) | y E x }
   and prove:
   - Membership preservation and reflection: y E x iff pi(y) in pi(x).
   - Injectivity of pi under extensionality of E.
   - Transitivity of the image set M = range(pi).
   - Uniqueness of the collapse isomorphism.
5. Implement an algorithmic reference implementation in Python under `jech/mostowski.py` with full verification functions for well-foundedness, extensionality, transitive closure, rank, and Mostowski collapse.
6. Provide comprehensive test suite in `tests/test_mostowski.py` and ensure zero Admitted in Coq proofs.

## Resolution Summary

### 1. Coq Formalization (`section_mostowski.v`)
- Formalized inductive well-founded relations, accessibility predicate `Acc`, and well-founded induction.
- Transitive closure `TC` and relation closure `in_TC`, proving transitivity, step inclusion, and well-foundedness transfer via `wf_clos_trans`.
- Inductive ordinal type `Ord` (zero, successor, supremum) with order `OLess`, accessibility-based recursion `rank_acc`, proof irrelevance `rank_acc_irrel`, and strict monotonicity `rank_strictly_increasing`.
- Hereditary sets `MSet`, membership `In_MSet`, transitive set predicate `is_transitive`.
- Mostowski collapse function `pi_acc`, proof irrelevance `pi_acc_irrel`, unfolding equation `pi_unfold`.
- Forward preservation `pi_rel_forward`, backward reflection `pi_rel_backward`, image set transitivity `mostowski_transitive`.
- Constructive injectivity `mostowski_injective`, isomorphism package `mostowski_isomorphism`, and uniqueness `mostowski_uniqueness`.
- Concrete von Neumann ordinals (empty, singleton, pair, 0, 1, 2) with verified membership lemmas.
- Compiled with 0 `Admitted` and 0 `admit`.

### 2. Python Reference Implementation (`jech/mostowski.py`)
- Algorithmic well-foundedness detection `is_well_founded` and minimal element search `find_minimal_element`, `is_minimal`.
- Extensionality checker `is_extensional`.
- Transitive closure relation `transitive_closure_relation` and element closure `transitive_closure`.
- Inductive rank calculation `rank` with cycle detection.
- Mostowski collapse computation `mostowski_collapse` returning `(collapse_map, transitive_set)` with `frozenset` representations.
- Transitive set verifier `is_transitive_set`.
- Von Neumann ordinal generator `von_neumann_ordinal`.
- Full isomorphism verifier `verify_mostowski_isomorphism`.
- High-level structure wrapper `WellFoundedStructure`.
- Exported in `jech/__init__.py`.

### 3. Test Suite and Verification (`tests/test_mostowski.py`)
- 44 total unit tests executed via `python3 verify.py`, covering well-foundedness, extensionality, transitive closure, rank, collapse, von Neumann sets, and Coq proof integrity.
- Zero `Admitted` and zero `admit` in Coq files verified automatically.
- Integrated into `Makefile` and `check.sh`.
