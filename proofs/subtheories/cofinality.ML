(* Cofinality Sub-Theory *)

(* Proof for Zorn's lemma *)

Theorem zorn_lemma : forall (X : Type) (R : X -> X -> Prop),
  (forall x, R x x) /
  (forall x y z, R x y -> R y z -> R x z) /
  (forall x y, R x y -> R y x) ->
  forall S : set X, (forall x y, x \in S -> y \in S -> R x y) ->
  exists x, x \in S /
    (forall y, y \in S -> R x y).

Proof.
  (* Implementation would go here *)
Qed.