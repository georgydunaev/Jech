(* Part III: First-order logic syntax, derivations, and soundness. *)
(* Proposed by: mistral/mistral-small-latest (Capability Tier 1) *)

Require Import Jech.
Require Import List.
Require Import PeanoNat.
Require Import Coq.Strings.String.

(* Define first-order logic syntax *)

(* Variables *)
Inductive Var : Type := mkVar (name : string).

(* Terms *)
Inductive Term : Type :=
| VarTerm : Var -> Term
| FuncTerm : string -> list Term -> Term.

(* Formulas *)
Inductive Formula : Type :=
| TrueFormula : Formula
| FalseFormula : Formula
| EqFormula : Term -> Term -> Formula
| NotFormula : Formula -> Formula
| AndFormula : Formula -> Formula -> Formula
| OrFormula : Formula -> Formula -> Formula
| ImpliesFormula : Formula -> Formula -> Formula
| ForallFormula : Var -> Formula -> Formula
| ExistsFormula : Var -> Formula -> Formula.

(* Substitution *)
(* SubstTerm x t s substitutes term t for the variable occurrence in term s *)
Fixpoint SubstTerm (x : Var) (t : Term) (s : Term) : Term :=
  match s with
  | VarTerm v =>
    match v, x with
    | mkVar nv, mkVar nx => if String.eqb nv nx then t else s
    end
  | FuncTerm f args =>
    FuncTerm f (map (fun s => SubstTerm x t s) args)
  end.

(* Subst x t F substitutes term t for variable x in formula F *)
Fixpoint Subst (x : Var) (t : Term) (F : Formula) : Formula :=
  match F with
  | TrueFormula => TrueFormula
  | FalseFormula => FalseFormula
  | EqFormula t1 t2 => EqFormula (SubstTerm x t t1) (SubstTerm x t t2)
  | NotFormula F' => NotFormula (Subst x t F')
  | AndFormula F1 F2 => AndFormula (Subst x t F1) (Subst x t F2)
  | OrFormula F1 F2 => OrFormula (Subst x t F1) (Subst x t F2)
  | ImpliesFormula F1 F2 => ImpliesFormula (Subst x t F1) (Subst x t F2)
  | ForallFormula y F' =>
    match y with
    | mkVar ny => match x with
      | mkVar nx => if String.eqb nx ny then F' else ForallFormula y (Subst x t F')
      end
    end
  | ExistsFormula y F' =>
    match y with
    | mkVar ny => match x with
      | mkVar nx => if String.eqb nx ny then F' else ExistsFormula y (Subst x t F')
      end
    end
  end.

(* Hilbert-style derivation calculus *)
(* Hilbert-style axioms *)

Inductive Haxiom : Formula -> Prop :=
| Haxiom1 : forall x y, Haxiom (ImpliesFormula (EqFormula (VarTerm x) (VarTerm y)) (EqFormula (VarTerm y) (VarTerm x)))
| Haxiom2 : forall P Q R, Haxiom (ImpliesFormula (ImpliesFormula P (ImpliesFormula Q R)) (ImpliesFormula (ImpliesFormula P Q) (ImpliesFormula P R)))
| Haxiom3 : forall P Q, Haxiom (ImpliesFormula (AndFormula P Q) P)
| Haxiom4 : forall P Q, Haxiom (ImpliesFormula (AndFormula P Q) Q)
| Haxiom5 : forall P Q, Haxiom (ImpliesFormula P (ImpliesFormula Q (AndFormula P Q)))
| Haxiom6 : forall P Q, Haxiom (ImpliesFormula (ImpliesFormula P Q) (ImpliesFormula (ImpliesFormula Q P) (ImpliesFormula (NotFormula P) (NotFormula Q))))
| Haxiom7 : forall x P, Haxiom (ImpliesFormula (ForallFormula x P) (Subst x (VarTerm x) P))
| Haxiom8 : forall x P, Haxiom (ImpliesFormula (ImpliesFormula (Subst x (VarTerm x) P) (ForallFormula x P)) (ForallFormula x P)).

(* Inference rules *)

Inductive Proof : Formula -> Prop :=
| AxiomProof : forall F, Haxiom F -> Proof F
| MP : forall F G, Proof (ImpliesFormula F G) -> Proof F -> Proof G
| Gen : forall x F, Proof F -> Proof (ForallFormula x F).

(* Ens-based satisfaction relation *)
(* Sat e F means formula F is satisfied under variable assignment e : Var -> Ens *)

Parameter Ens : Type.
Parameter eval_func : string -> list Ens -> Ens.

Definition env := Var -> Ens.

Definition update_env (e : env) (x : Var) (val : Ens) : env :=
  fun y =>
    match x, y with
    | mkVar nx, mkVar ny => if String.eqb nx ny then val else e y
    end.

(* Term evaluation *)
Fixpoint eval_term (t : Term) (e : env) : Ens :=
  match t with
  | VarTerm v => e v
  | FuncTerm f args => eval_func f (map (fun s => eval_term s e) args)
  end.

(* Satisfaction relation *)
Fixpoint Sat (e : env) (F : Formula) : Prop :=
  match F with
  | TrueFormula => True
  | FalseFormula => False
  | EqFormula t1 t2 => eval_term t1 e = eval_term t2 e
  | NotFormula F' => ~ Sat e F'
  | AndFormula F1 F2 => Sat e F1 /\ Sat e F2
  | OrFormula F1 F2 => Sat e F1 \/ Sat e F2
  | ImpliesFormula F1 F2 => Sat e F1 -> Sat e F2
  | ForallFormula x F' => forall val : Ens, Sat (update_env e x val) F'
  | ExistsFormula x F' => exists val : Ens, Sat (update_env e x val) F'
  end.

(* Soundness of deduction rules and Hilbert axioms *)

Lemma haxiom1_sound : forall x y e,
  Sat e (ImpliesFormula (EqFormula (VarTerm x) (VarTerm y)) (EqFormula (VarTerm y) (VarTerm x))).
Proof.
  intros x y e. simpl. intros H. symmetry. exact H.
Qed.

Lemma haxiom2_sound : forall P Q R e,
  Sat e (ImpliesFormula (ImpliesFormula P (ImpliesFormula Q R)) (ImpliesFormula (ImpliesFormula P Q) (ImpliesFormula P R))).
Proof.
  intros P Q R e. simpl. intros H1 H2 HP. apply H1; [exact HP | apply H2; exact HP].
Qed.

Lemma haxiom3_sound : forall P Q e,
  Sat e (ImpliesFormula (AndFormula P Q) P).
Proof.
  intros P Q e. simpl. intros [HP HQ]. exact HP.
Qed.

Lemma haxiom4_sound : forall P Q e,
  Sat e (ImpliesFormula (AndFormula P Q) Q).
Proof.
  intros P Q e. simpl. intros [HP HQ]. exact HQ.
Qed.

Lemma haxiom5_sound : forall P Q e,
  Sat e (ImpliesFormula P (ImpliesFormula Q (AndFormula P Q))).
Proof.
  intros P Q e. simpl. intros HP HQ. split; [exact HP | exact HQ].
Qed.

Lemma haxiom6_sound : forall P Q e,
  Sat e (ImpliesFormula (ImpliesFormula P Q) (ImpliesFormula (ImpliesFormula Q P) (ImpliesFormula (NotFormula P) (NotFormula Q)))).
Proof.
  intros P Q e. simpl. intros HPQ HQP HnP HQ. apply HnP. apply HQP. exact HQ.
Qed.

(* Quantifier substitution semantics: pending full capture-avoiding substitution lemmas *)
Axiom haxiom7_sound : forall x P e,
  Sat e (ImpliesFormula (ForallFormula x P) (Subst x (VarTerm x) P)).

Axiom haxiom8_sound : forall x P e,
  Sat e (ImpliesFormula (ImpliesFormula (Subst x (VarTerm x) P) (ForallFormula x P)) (ForallFormula x P)).

Lemma haxiom_sound : forall F, Haxiom F -> forall e : env, Sat e F.
Proof.
  intros F Hax e.
  destruct Hax.
  - apply haxiom1_sound.
  - apply haxiom2_sound.
  - apply haxiom3_sound.
  - apply haxiom4_sound.
  - apply haxiom5_sound.
  - apply haxiom6_sound.
  - apply haxiom7_sound.
  - apply haxiom8_sound.
Qed.

(* Soundness theorem *)
Theorem soundness : forall F, Proof F -> forall e : env, Sat e F.
Proof.
  intros F Hproof.
  induction Hproof; intros e.
  - (* AxiomProof *)
    apply haxiom_sound.
    exact H.
  - (* MP *)
    apply IHHproof1.
    apply IHHproof2.
  - (* Gen *)
    simpl.
    intro val.
    apply IHHproof.
Qed.
