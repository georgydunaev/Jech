(* Part III: Development of formulas and derivations. *)

(* The `Fo` inductive type represents formulas in a logical system. It includes constructors for predicates, equality, logical connectives, and quantifiers. See also: `Part_II` for the development of the logical system, `Part_IV` for the application of the theorems, and the `Examples` section for usage examples. Additionally, refer to `Theorem_1` in `Part_V` for an application of these formulas. *)

(* Detailed Explanation: *)
(* The `Fo` type is defined inductively with several constructors: *)
(* - `Pred` represents a predicate with a natural number identifier and a list of natural number arguments. *)
(* - `Eq` represents an equality between two natural numbers. *)
(* - `And`, `Or`, `Imp` represent logical connectives for conjunction, disjunction, and implication, respectively. *)
(* - `Not` represents a logical negation. *)
(* - `Forall` and `Exists` represent universal and existential quantification over a natural number variable, respectively. *)

Section Part_III.

(* Development of formulas and derivations. *)

(* The `Fo` inductive type represents formulas in a logical system. It includes constructors for predicates, equality, logical connectives, and quantifiers. See also: `Part_II` for the development of the logical system, `Part_IV` for the application of the theorems, and the `Examples` section for usage examples. Additionally, refer to `Theorem_1` in `Part_V` for an application of these formulas. *)

(* Detailed Explanation: *)
(* The `Fo` type is defined inductively with several constructors: *)
(* - `Pred` represents a predicate with a natural number identifier and a list of natural number arguments. *)
(* - `Eq` represents an equality between two natural numbers. *)
(* - `And`, `Or`, `Imp` represent logical connectives for conjunction, disjunction, and implication, respectively. *)
(* - `Not` represents a logical negation. *)
(* - `Forall` and `Exists` represent universal and existential quantification over a natural number variable, respectively. *)
Inductive Fo : Type :=
(* `Pred` represents a predicate with a natural number identifier and a list of natural number arguments. *)
| Pred (n:nat) (args:list nat)
(* `Eq` represents an equality between two natural numbers. *)
| Eq (t1 t2:nat)
(* `And` represents a logical conjunction of two formulas. *)
| And (f1 f2:Fo)
(* `Or` represents a logical disjunction of two formulas. *)
| Or (f1 f2:Fo)
(* `Imp` represents a logical implication between two formulas. *)
| Imp (f1 f2:Fo)
(* `Not` represents a logical negation of a formula. *)
| Not (f:Fo)
(* `Forall` represents a universal quantification over a natural number variable in a formula. *)
| Forall (x:nat) (f:Fo)
(* `Exists` represents an existential quantification over a natural number variable in a formula. *)
| Exists (x:nat) (f:Fo). 
| Pred (n:nat) (args:list nat)
| Eq (t1 t2:nat)
| And (f1 f2:Fo)
| Or (f1 f2:Fo)
| Imp (f1 f2:Fo)
| Not (f:Fo)
| Forall (x:nat) (f:Fo)
| Exists (x:nat) (f:Fo).

(* Example usage of the `Fo` type: *)

(* Additional Examples: *)
(* Constructing a logical disjunction formula: *)
Example or_example : Fo := Or (Eq 2 3) (Pred 1 [2; 3]).

(* Constructing a logical implication formula: *)
Example imp_example : Fo := Imp (Eq 2 3) (Pred 1 [2; 3]).

(* Constructing a logical negation formula: *)
Example not_example : Fo := Not (Eq 2 3).

(* Constructing an existential quantification formula: *)
Example exists_example : Fo := Exists 1 (Eq 1 2).
(* Constructing a predicate formula: *)
Example predicate_example : Fo := Pred 1 [2; 3].

(* Constructing an equality formula: *)
Example equality_example : Fo := Eq 2 3.

(* Constructing a logical conjunction formula: *)
Example and_example : Fo := And (Eq 2 3) (Pred 1 [2; 3]).

(* Constructing a universal quantification formula: *)
Example forall_example : Fo := Forall 1 (Eq 1 2).

End Part_III.