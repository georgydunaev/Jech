From ZFC Require Import Sets Axioms.

Notation "x '==' y" :=(EQ x y) (at level 140).
Check Ens.
Definition appli (x':Ens) (y':Ens->Prop) := y' x'.

Class tIN (A:Type) := tin : Ens -> A -> Prop.
Instance sIN : tIN Ens := IN.
Instance cIN : tIN (Ens->Prop) := appli.
Notation " x ∈ y " :=(tin x y) (at level 50
(*, y at level 159*)).
Notation " { x }` ":=(Sing x).
(*Notation " '{' x ',' y '}`' ":=(Paire x y)
(format "'{' x ',' y '}`'")
.*)
Check fun x => (x ∈ { x }`).

Theorem t1 (x:Ens) : x ∈ { x }`.
Proof.
unfold tin, sIN.
unfold Sing.
unfold Paire.
simpl.
exists true.
simpl.
apply EQ_refl.
Defined.

(* ================END================= *)

unfold tIN.

End s1.
si

| T_Var1 : forall G T,
    G ⊢ tvar1 :: T

Instance sIN Ens : tIN Ens := Build_tIN IN.
(*{
  fi:Ens->A->Prop;
  pr:fi x y;
}.*)

Check tIN Ens.

Instance sIN Ens (x:Ens) (y:Ens) : tIN Ens x y 
:= (j:IN x y).







Class tIN (A:Type) (fi:Ens->A->Prop) (x:Ens)(y:A):= 
{
 pr:fi x y;
}.

(*todo function that 
Ens |-> IN
Ens->Prop |-> appli
*)
Definition fu (A:Type) : Ens->A->Prop.

Instance sIN  (x:Ens) (y:Ens) (j:IN x y) : tIN Ens IN x y
 := (Build_tIN Ens IN x y j).
Instance cIN  (x:Ens) (y:Ens->Prop) (j: y x) 
: tIN (Ens->Prop) appli x y
 := (Build_tIN (Ens->Prop) appli x y j).
Check cIN.

(*
Class tIN (A:Type) (fi:Ens->A->Prop) := 
{
 x:Ens;
 y:A;
 pr:fi x y;
}.

Instance sIN  x y (j:IN x y) : tIN Ens IN := (Build_tIN Ens IN x y j).
Check sIN.
*)

Notation "x '∈' y" :=(tIN _ _ x y) (at level 40).
Theorem t1 x : x ∈ (Sing x).
apply Build_tIN.
simpl.
exists true.
simpl.
apply EQ_refl.
Defined.

Theorem t1 x : tIN Ens IN x (Sing x).
pro (IN x Y).
(* TODO Определить операцию на классе и перенести её на множества. *)
Section 
