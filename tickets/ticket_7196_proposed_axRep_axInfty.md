# [Jech · PROPOSED] Prove the remaining ZFC axioms internally (`axRep`, `axInfty`)

**Proposed by**: `opencode/glm-5.3-flash-free` (Capability Tier 1) during Pass 1/5 (Ticket #7196)
**Parent ticket**: `ticket_7196_zone_delegated.md`

## Observation

Part I of `Jech.v` derives most ZFC axioms as theorems on the Scott-style
`Ens` trees, none of which can be automated — every definition in Part II
must be presumed *unsafe until its soundness proof is checked*:

- `axUnion` (line ~955), `axPower` (line ~969), `axReg` (line ~1114),
  `axChoice` (line ~3289) are done;
- extensionality follows from the bisimulation `EQ`;
- **replacement and infinity are only imported** through the type-level
  constructor `sup : forall A, (A -> Ens) -> Ens` plus the external axiom
  `Axiom axSFC : SetoidFunctionalChoice` (line ~43 region) and
  `IndefiniteDescription`.

## Proposed work

1. Attempt an internal statement and proof of replacement (`axRep`) on `Ens`:
   for an `Ens`-small index type `I`, image of a set under a functional
   class is a set (this is essentially what `sup` guarantees — make it a
   theorem in the *internal* set/class language of Part IV).
2. Attempt an internal `axInfty` theorem by constructing the von Neumann
   naturals as an `Ens` and exhibiting an inductive set, reusing
   `Ind`, `pTr`, and the `ex_1_3`–`ex_1_6` machinery of Part II.
3. Reduce the assumed strength of `axSFC` where possible; the author's TODO
   in the header ("try to use the constructible universe to avoid axSFC and
   LEM") is exactly this direction — even a partial reduction should be
   recorded in a dedicated comment block, not by rewriting existing proofs.

## Acceptance criteria

- Theorems named `axRep` and/or `axInfty` compile and are catalogued in the
  file's header exercise/axiom index.
- Existing statements, comments, and dead-end proofs remain untouched.
