Axiom Ens : Set.
Axiom tin : Ens -> Ens -> Prop.
Axiom Sing : Ens -> Ens.

(*Axiom A:Type.
Definition Ens := A -> Prop.
Definition tin x (s:Ens) := s x.
Definition Sing x : Ens := eq x.*)

Section FixingBraceNotation.
  Notation "x  ∈  y" := (tin x y) (at level 50).
  (* Note: the level on the following modifier is already set for this
  notation and so is redundant, but it needs to be reproduced exactly if
  you add a format modifier (you can overwrite the notation but not the
  parsing levels). *)
  Notation "{ x }" := (Sing x) (at level 0, x at level 99).
  Notation "x  ∈  { y }" := (tin x (Sing y)) (at level 50).
  Check fun x => (x ∈ { x }).
  Check fun x => {x}.
End FixingBraceNotation.

Section RemovingWhitespace.
  Notation "x  ∈  y" := (tin x y) (at level 50).
  Notation "{ x }`" := (Sing x) (at level 0, format "{ x }`").
  Check fun x => (x ∈ { x }`).
End RemovingWhitespace.

Section AddingWhitespace.
  Notation "x  ∈  y" := (tin x y) (at level 50).
  Notation "{  x  }`" := (Sing x) (at level 0).
  Check fun x => (x ∈ {x}`).
End AddingWhitespace.
