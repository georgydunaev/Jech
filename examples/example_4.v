(* Advanced example: Formulating set-theoretic axioms as first-order formulas *)

Require Import Jech.
Require Import List.
Import ListNotations.

(* Axiom of Infinity represented as a first-order formula in Fo *)
Definition infinity_formula : Fo :=
  Jech.Exists 0 (Jech.Forall 1 (Imp (Pred 0 [1]) (Jech.Exists 2 (And (Pred 0 [2]) (Pred 1 [1; 2]))))).

(* Axiom of Power Set represented in Fo *)
Definition power_set_formula : Fo :=
  Jech.Forall 0 (Jech.Exists 1 (Jech.Forall 2 (Imp (Pred 0 [2; 1]) (Jech.Forall 3 (Imp (Pred 0 [3; 2]) (Pred 0 [3; 0])))))).

Example formulas_well_formed :
  size infinity_formula >= 1 /\ size power_set_formula >= 1.
Proof.
  split; apply size_ge_one.
Qed.

(* End of example. *)
