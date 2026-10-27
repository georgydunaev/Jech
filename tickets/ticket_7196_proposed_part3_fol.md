# [Jech · PROPOSED] Expand Part III: first-order logic (syntax, derivations, soundness)

**Proposed by**: `opencode/glm-5.3-flash-free` (Capability Tier 1) during Pass 1/5 (Ticket #7196)
**Parent ticket**: `ticket_7196_zone_delegated.md`

## Observation

Part III of `Jech.v` (line ~2174) is an explicitly announced but still empty
section. The author's header says:

> Part III(empty): Development of formulas and derivations.

The ambition stated in the top header is a *self-contained book* of
first-order logic and ZFC in Coq, so a standalone FOL chapter (syntactic
formulas `Fo` already have a Metamath-style prototype at line ~4624 in
Part V) fits the roadmap.

## Proposed work

1. Define an inductive syntactic representation of first-order formulas
   (either extend the existing `Inductive Fo` or factor it out into Part III).
2. Implement a Hilbert-style or natural-deduction derivation calculus for it.
3. Prove soundness of the calculus wrt. the `Ens`-based satisfaction relation.
4. Keep the existing Part V `Fo` untouched (audit-trail policy); prefer a
   Part III-local copy or generalization.

## Acceptance criteria

- New `Section Part_III` compiles with `coqc -Q . '' Jech.v`.
- No existing definitions or commented-out blocks are modified or removed.
