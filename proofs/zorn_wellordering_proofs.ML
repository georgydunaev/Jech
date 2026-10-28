(* Proofs for Zorn's lemma and Well-Ordering theorem *)

(* Proof for Zorn's lemma *)

Theorem zorn_lemma : forall (X : Type) (R : X -> X -> Prop),
  (forall x, R x x) /
  (forall x y z, R x y -> R y z -> R x z) /
  (forall x y, R x y -> R y x) ->
  forall S : set X, (forall x y, x \in S -> y \in S -> R x y) ->
  exists x, x \in S /
    (forall y, y \in S -> R x y).
Proof.
  intros X R refl trans antisym S chain.
  destruct (well_founded R) as [wf].
  exists (wf_induction wf S chain).
  intros x Hx y Hy.
  apply antisym.
  apply trans.
  apply Hx.
  apply Hy.
Qed.

(* Proof for Well-Ordering theorem *)

Theorem well_ordering : forall (X : Type) (R : X -> X -> Prop),
  (forall x, R x x) /
  (forall x y z, R x y -> R y z -> R x z) /
  (forall x y, R x y -> R y x) ->
  forall S : set X, S \neq \emptyset ->
  exists x, x \in S /
    (forall y, y \in S -> R x y).
Proof.
  intros X R refl trans antisym S H.
  destruct (well_founded R) as [wf].
  exists (wf_induction wf S (fun x => x \in S)).
  intros x Hx y Hy.
  apply antisym.
  apply trans.
  apply Hx.
  apply Hy.
Qed.