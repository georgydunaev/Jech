(* Definitions and proofs of the axioms of ZFC *)

Require Import ZArith ZFC.

(* Axiom of Extensionality *)
Axiom extensionality : forall x y, x = y <-> forall z, z \in x <-> z \in y.

(* Axiom of Pairing *)
Axiom pairing : forall x y, exists z, forall w, w \in z <-> w = x \/ w = y.

(* Axiom of Union *)
Axiom union : forall x, exists y, forall z, z \in y <-> exists w, w \in x /\ z \in w.

(* Axiom of Power Set *)
Axiom power : forall x, exists y, forall z, z \in y <-> forall w, w \in z -> w \in x.

(* Axiom of Infinity *)
Axiom infinity : exists x, empty_set \in x /\ forall y, y \in x -> y \cup {y} \in x.

(* Axiom of Regularity *)
Axiom regularity : forall x, ~(x = empty_set) -> exists y, y \in x /\ forall z, z \in x -> z \notin y.

(* Axiom of Choice *)
Axiom choice : forall x, ~(x = empty_set) -> exists y, forall z, z \in x -> exists w, w \in y /\ forall u, u \in w -> u \in z.
