# Changes for Ticket 7441

## Notation Standardization

1. Standardize the notation for forcing axioms and poset definitions.
2. Decouple dense set predicates from the main definitions.

## Implementation Plan

1. Update the `axRep_axInfty.ML` file with standardized notation.
2. Create a new file for dense set predicates.
3. Update the test cases to reflect these changes.

## Progress

- [x] Full repo survey (2026-10-30, worker `opencode/glm-5.3-flash-free`)
- [x] Verdict: NOT APPLICABLE
- [ ] Notation standardization completed *(nothing to standardize — see Verdict)*
- [ ] Dense set predicates decoupled *(no dense predicates exist)*
- [ ] Test cases updated *(none affected)*

## Verdict

Exhaustive `grep -rnil` over `Jech.v`, `Part_III.v`, `examples/`, `src/`, `proofs/`,
`axInfty.ML`, and `section_ex_1_6.ML` found **zero** occurrences of forcing, poset,
or dense-set material (search terms: `forc*`, `poset`, `dense`, `Generic`).
The repository currently contains only the ZFC axiom work (`axRep`, `axInfty`),
Zorn / well-ordering proofs, and the Section 1.6 exercise chain — no Chapter 7
forcing development has ever been written here, so there are no forcing axiom
definitions to clean up and no poset notations to standardize.

Introducing an entire forcing theory would be new scope (Ticket-level development
work), not the cosmetic cleanup this ticket requests, and is therefore out of
scope. Ticket should be re-scoped if forcing content is later added.

### Test state observed at conclusion
- Poly/ML check: `proofs/axRep_axInfty_proofs.ML` loads with no errors.
-Poly/ML static errors remain (pre-existing) for the Coq-syntax transcripts
  `proofs/zorn_wellordering_proofs.ML`, `section_ex_1_6.ML`, `axInfty.ML`
  (these are Coq proofs that historically require `coqc`, which is not installed
  at `/usr/bin/coqc`; `check.sh` therefore cannot run either — pre-existing
  environment issue, unchanged by this ticket).
- No code files touched by this ticket; no regressions introduced.
