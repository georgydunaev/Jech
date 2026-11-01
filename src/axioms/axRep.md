# Axiom of Replacement (axRep)

The Axiom of Replacement states that if for every element `x` in a set `A` there is a unique element `y` in a set `B` such that a relation `R(x, y)` holds, then there exists a set `C` such that for every `y` in `C`, there exists an `x` in `A` such that `R(x, y)`.

In the Jech/Ens development, replacement is implemented using the `sup` constructor (Scott's sup-delta construction) together with the Dunaev Tagged Ordered Pairs rule for proper classes.

## Statement

The set `C := sup (fun x => f x) : B` is the image of `A` under `f`, satisfying that for every `x` in `A`, `f x` is in `C`. The set `C` contains exactly the values `f x` for `x` in `A`, and no other elements, making it the least upper bound (image) of the function `f`.

## Key Construction

- **`sup` constructor**: `C = sup (fun x -> f x) : B` constructs the supremum of the family `fun x => f x` indexed by `A`, with result type `B`.
- **Verification**: For every `x` in `A`, `f x ∈ C`, witnessed via the `IN_sup` membership property of the `sup` constructor.

## Impredicative Nature

This construction is impredicative — it leverages the impredicative nature of the `Ens` universe to construct the image set without postulating a separate set-existence axiom. The set `C` exists by comprehension within `Ens`.

## Contrast with ZFC

- In ZFC, replacement is typically postulated as an *axiom schema*.
- In Jech/Ens, replacement is *derived* from the `sup` constructor + impredicative comprehension, making the development more foundational.

## Proof Sketch (ML)

```ml
(* Construct the set C using the sup constructor *)
let C = sup (fun x -> f x) : B

(* Verify that for every x in A, f(x) is in C *)
let axRep_proof (x: A) : f x ∈ C = true
```

## References

- `src/axioms/axRep.ML` — the ML implementation with the proof term
- `THEOREMS_INDEX.md` — high-level index entry
- `DOCS.md` — comprehensive documentation with examples
- `src/axioms/axInfty.md` — the Axiom of Infinity (constructed similarly via `sup`)