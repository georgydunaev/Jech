# [Jech · PROPOSED] Complete the `ex_1_6` Chapter-1 exercise chain

**Proposed by**: `opencode/glm-5.3-flash-free` (Capability Tier 1) during Pass 1/5 (Ticket #7196)
**Parent ticket**: `ticket_7196_zone_delegated.md`

## Observation

The `ex_1_6` chain (Jech's *Set Theory*, Chapter 1, Exercise 1.6; section
`Section ex_1_6.` at line ~1965) already shows substantial progress:
`ex_1_6_lem1`–`ex_1_6_lem5` are proved, and history shows the author working
through it in commits `begin of ex_1_6` → `ex_1_6 lemmas` → `some new ideas`.

Not every sub-obligation of Exercise 1.6 appears discharged yet; the theorem
stubs and supporting lemmas around lines 1965–2100 are the natural unit to
finish.

## Proposed work

1. Read the exact statement of Exercise 1.6 in Jech's *Set Theory* / IST.
2. Enumerate its sub-obligations and cross-check them against the existing
   `ex_1_6_lem*` lemmas and theorems in the section.
3. Implement any missing proofs, following the file's conventions:
   `_sound_*` side-conditions via `SoundPred`, and keep any alternative
   proof attempts side-by-side (mirroring the `ex_1_2 / ex_1_2' / ex_1_2''`
   multi-variant style).
4. Update the header index line `ex_1_6 : ex.1.6` only if a new sub-exercise
   id deserves its own entry.

## Acceptance criteria

- `coqc -Q . '' Jech.v` succeeds after the additions.
- No commented-out or alternative proof blocks are deleted.
