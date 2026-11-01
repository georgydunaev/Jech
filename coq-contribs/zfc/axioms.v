(* ZFC Axioms *)
(* This file contains the formal statements of the axioms of ZFC as Coq axioms.
   Note: These are stated as axioms (unproven) within this Coq development.
   Some axioms have corresponding proofs in `theorems.v` where applicable.
*)

(* ================================================================= *)
(* Axiom of Extensionality *)
(* ================================================================= *)
(* State: Two sets are equal iff they have exactly the same elements. *)
(* Formal: forall x y, x = y <-> forall z, z \in x <-> z \in y *)
Axiom extensionality : forall x y, x = y <-> forall z, z \in x <-> z \in y.

(* ================================================================= *)
(* Axiom of Pairing *)
(* ================================================================= *)
(* State: For any two sets x and y, there exists a set z whose
   elements are exactly x and y. *)
(* Formal: forall x y, exists z, forall w, w \in z <-> w = x \/ w = y *)
Axiom pairing : forall x y, exists z, forall w, w \in z <-> w = x \/ w = y.

(* ================================================================= *)
(* Axiom of Union *)
(* ================================================================= *)
(* State: For any set A, there exists a set B whose elements are
   exactly the elements of the elements of A. *)
(* Formal: forall x, exists y, forall z, z \in y <-> exists w, w \in x /\ z \in w *)
Axiom union : forall x, exists y, forall z, z \in y <-> exists w, w \in x /\ z \in w.

(* ================================================================= *)
(* Axiom of Power Set *)
(* ================================================================= *)
(* State: For any set x, there exists a set y whose elements are
   exactly the subsets of x. *)
(* Formal: forall x, exists y, forall z, z \in y <-> forall w, w \in z -> w \in x *)
Axiom power : forall x, exists y, forall z, z \in y <-> forall w, w \in z -> w \in x.

(* ================================================================= *)
(* Axiom of Infinity *)
(* ================================================================= *)
(* State: There exists an inductive set containing the empty set
   and closed under the successor operation. *)
(* Formal: exists x, empty_set \in x /\ forall y, y \in x -> y \cup {y} \in x *)
Axiom infinity : exists x, empty_set \in x /\ forall y, y \in x -> y \cup {y} \in x.

(* ================================================================= *)
(* Axiom of Regularity (Foundation) *)
(* ================================================================= *)
(* State: Every non-empty set x has an element y that is disjoint
   from x (i.e., no element of y is also an element of x). *)
(* Formal: forall x, ~(x = empty_set) -> exists y, y \in x /\ forall z, z \in x -> z \notin y *)
Axiom regularity : forall x, ~(x = empty_set) -> exists y, y \in x /\ forall z, z \in x -> z \notin y.

(* ================================================================= *)
(* Axiom of Choice *)
(* ================================================================= *)
(* State: For any non-empty set x, there exists a choice function y
   that selects an element from each set in x. *)
(* Formal: forall x, ~(x = empty_set) -> exists y, forall z, z \in x -> exists w, w \in y /\ forall u, u \in w -> u \in z *)
Axiom choice : forall x, ~(x = empty_set) -> exists y, forall z, z \in x -> exists w, w \in y /\ forall u, u \in w -> u \in z.
