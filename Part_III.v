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

End Part_III.

(* Hilbert-style derivation calculus *)

(* Axioms *)Inductive Axiom : Formula -> Prop :=
| Axiom1 : forall x y, Axiom (ImpliesFormula (ImpliesFormula (ImpliesFormula (NotFormula (EqFormula (VarTerm x) (VarTerm y))) (NotFormula (EqFormula (VarTerm y) (VarTerm x)))) (EqFormula (VarTerm x) (VarTerm y))))
| Axiom2 : forall P Q R, Axiom (ImpliesFormula (ImpliesFormula (ImpliesFormula P (ImpliesFormula Q R)) (ImpliesFormula (ImpliesFormula P Q) (ImpliesFormula P R)))
| Axiom3 : forall P Q, Axiom (ImpliesFormula (AndFormula P Q) P)
| Axiom4 : forall P Q, Axiom (ImpliesFormula (AndFormula P Q) Q)
| Axiom5 : forall P Q, Axiom (ImpliesFormula P (ImpliesFormula Q (AndFormula P Q)))
| Axiom6 : forall P Q, Axiom (ImpliesFormula (ImpliesFormula P Q) (ImpliesFormula (ImpliesFormula Q P) (ImpliesFormula (NotFormula P) (NotFormula Q))))
| Axiom7 : forall x P, Axiom (ImpliesFormula (ForallFormula x P) (Subst x (VarTerm x) P))
| Axiom8 : forall x P, Axiom (ImpliesFormula (ImpliesFormula (Subst x (VarTerm x) P) (ForallFormula x P)) (ForallFormula x P)).

(* Inference rules *)Inductive Proof : Formula -> Prop :=
| AxiomProof : forall F, Axiom F -> Proof F
| MP : forall F G, Proof (ImpliesFormula F G) -> Proof F -> Proof G
| Gen : forall x F, Proof F -> Proof (ForallFormula x F).
| TrueFormula : Formula
| FalseFormula : Formula
| EqFormula : Term -> Term -> Formula
| NotFormula : Formula -> Formula
| AndFormula : Formula -> Formula -> Formula
| OrFormula : Formula -> Formula -> Formula
| ImpliesFormula : Formula -> Formula -> Formula
| ForallFormula : Var -> Formula -> Formula
| ExistsFormula : Var -> Formula -> Formula.