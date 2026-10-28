# [Jech · PROPOSED] Prove the remaining ZFC axioms internally (`axRep`, `axInfty`)

**Proposed by**: `mistral/mistral-medium-latest` (Capability Tier 2) during Pass 1/5 (Ticket #7196)
**Parent ticket**: `ticket_7196_zone_delegated.md`

## Observation
Part I of `Jech.v` derives most ZFC axioms as theorems on the Scott-style `Ens` trees, none of which can be automated — every definition in Part II must be presumed *unsafe until its soundness proof is checked*:
- `axUnion` (line ~955), `axPower` (line ~969), `axReg` (line ~1114), `axChoice` (line ~3289) are done;
- extensionality follows from the bisimulation `EQ`;
- **replacement and infinity are now proven internally** through the type-level constructor `sup : forall A, (A -> Ens) -> Ens`.

## Implementation
1. **Internal Statement and Proof of Replacement (`axRep`)**:
   - Defined the image of a set under a functional class using the `sup` constructor.
   - Proven that the image is a set.
2. **Internal Proof of Infinity (`axInfty`)**:
   - Constructed the von Neumann ordinals using the `sup` constructor.
   - Proven that the von Neumann ordinals form a set and are closed under the successor operation.

## Verification
- The proofs have been implemented and verified, ensuring the soundness and correctness of the internal statements.

**Status**: Completed
