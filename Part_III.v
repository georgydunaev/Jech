(* Part III: First-order logic syntax, derivations, and soundness. *)
(* Proposed by: mistral/mistral-small-latest (Capability Tier 1) *)

Require Import Jech.

Section Part_III.

(* Define first-order logic syntax *)

(* Variables *)Inductive Var : Type := mkVar (name : string).

(* Terms *)Inductive Term : Type :=
| VarTerm : Var -> Term
| FuncTerm : string -> list Term -> Term.

(* Formulas *)Inductive Formula : Type :=
| TrueFormula : Formula
| FalseFormula : Formula
| EqFormula : Term -> Term -> Formula
| NotFormula : Formula -> Formula
| AndFormula : Formula -> Formula -> Formula
| OrFormula : Formula -> Formula -> Formula
| ImpliesFormula : Formula -> Formula -> Formula
| ForallFormula : Var -> Formula -> Formula
| ExistsFormula : Var -> Formula -> Formula.