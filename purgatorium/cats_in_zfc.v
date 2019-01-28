From ZFC Require Import Sets Axioms Cartesian Omega.
Require Classical_Prop Classical_Pred_Type.

(*
Inductive qwe (S : Ens) : Type :=
| con1 : forall q:Ens, (IN q S) -> qwe S.*)

Definition E := Ens.

(*Inductive qwe : E -> Type :=
| con1 : forall S:Ens, qwe S.*)

(* Interpretation of sets as types.
Types are consist of equivalence classes of terms of type . *)
Inductive interp (S : Ens) : Type :=
| con1 : forall q:Ens, (IN q S) -> interp S.

(*Coercion cip := interp.*)
Coercion interp : Ens >-> Sortclass.

Definition R {x:E} : x -> E.
Proof.
intros H.
destruct H as [q].
exact q.
Defined.


(*Parameter bij : Set -> Set -> Set.*)
Check IN : Ens -> Ens-> Prop.
(*bij is declared*)
Definition ap  : Ens -> Ens ->  Prop := fun x y => IN y x.
Coercion ap : Ens >-> Funclass.
Check IN_Sing.

Theorem visv : (Sing Vide) Vide.
Proof.
apply IN_Sing.
Defined.

(* 
Definition in2ap  : forall A B, IN A B -> B A 
:= fun x y H => H.
Coercion in2ap : Ens >-> Funclass.
Check IN_Sing.*)

Definition EQT (a b:Type) : Prop := exists (ae be:Ens),  True.

Theorem R_inj : forall (x:E) (a b : x), EQ (R a) (R b) -> a = b.
Proof.
intros x a b H.
unfold R in H.
destruct a as [Sa].
destruct b as [Sb].

apply f_equal.
simpl.
reflexivity.
Defined.

Definition inc (x y : E) := exists a : y, EQ (R a) x.

Definition sub (a b : E) := forall x : E, inc x a -> inc x b.

Theorem extensitonality : forall a b : E, sub a b -> sub b a -> EQ a b.
Proof.
intros a b asb bsa.
unfold sub in * |- *.
unfold inc in * |- *.
apply axExt.
intro z; split;intro h.
+
assert (exists a0 : a, EQ (R a0) a).
exists (con1 a).
Check (asb a).

eapply R_inj.

(*unfold qwe in H.*)
