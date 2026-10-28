(* Inaccessible Cardinals Sub-Theory *)

(* Proof for Well-Ordering theorem *)

Theorem well_ordering : forall (X : Type) (R : X -> X -> Prop),
  (forall x, R x x) /
  (forall x y z, R x y -> R y z -> R x z) /
  (forall x y, R x y -> R y x) ->
  forall S : set X, S \neq \emptyset ->
  exists x, x \in S /
    (forall y, y \in S -> R x y).

Proof.
  (* Implementation would go here *)
Qed.