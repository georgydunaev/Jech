# [Jech · PROPOSED] CI: `coqc`-based build check for `Jech.v`

**Proposed by**: `opencode/glm-5.3-flash-free` (Capability Tier 1) during Pass 1/5 (Ticket #7196)
**Parent ticket**: `ticket_7196_zone_delegated.md`

## Observation

The whole library is a single ~5.7k-line `Jech.v`; there is currently no
automated check that it still compiles. Regressions introduced by future
passes (this repo receives 5 carte-blanche passes, tickets #7196–#7200) can
only be caught by manual compilation.

Note: at the time of this ticket, the `Jech` development container does not
have `coqc` installed, so a `coq-community/ocaml-current` (or similar)
Docker-based CI image must be chosen. (Container-scope restriction: the
worker may not run Docker locally; CI must run on GitLab CI.)

## Proposed work

1. Add a minimal `Makefile` target, e.g. `make check` running
   `coqc -Q . '' Jech.v`, so a human or agent with Coq installed can verify
   quickly.
2. Add a `.gitlab-ci.yml` with a single `build` stage using a Coq image
   (e.g. `coqorg/coq`) compiling `Jech.v` and reporting failure at
   regression time.
3. `purgatorium/` files must explicitly **not** be built (they are a
   scratch workspace and are not guaranteed to compile); document this in
   the CI file as a comment so future passes don't "fix" it.

## Acceptance criteria

- `make check` (on any machine with Coq ≥ 8.x) compiles `Jech.v` cleanly.
- CI passes on `gitlab` remote (`http://127.0.0.1:8929/georgydunaev/Jech`).
- Pushes to public GitHub remain forbidden; CI runs on local GitLab only.
