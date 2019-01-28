(*=== There is THE OLD CODE below! ===*)

(*Require Import ClassicalChoice. choice
Theorem choice :
 forall (A B : Type) (R : A->B->Prop),
   (forall x : A, exists y : B, R x y) ->
    exists f : A->B, (forall x : A, R x (f x)).*)

Definition choice :=
  forall (A B : Type) (P : A -> B -> Prop),
  (forall a : A, (exists b : B, P a b)) ->
  (exists f : A -> B, forall a : A, P a (f a)).

Check sup.
(*Section sec_choice.*)
(*Context (AC : choice).*)
Section sec2.
Context (S:Ens).
Context (H:~IN Vide S).

(* попроще: *)
Section easy.
Definition A:=pi1 S.
Definition B:=pi1 (Union S).
Definition P:= fun ts tus => IN (pi2 (Union S) tus) (pi2 S ts).
Theorem hyp : forall a : A, (exists b : B, P a b).
Proof.
intro a.
unfold A, B, P in *|-*.
pose (XinS := lem4 S a). (*apply (lem4 S) in a as XinS.???*) (* 'IN X S' *)
pose (X:=pi2 S a). (* Множество 'X' соответствует терму 'a'.*)
(*'X' is nonempty *) 
(* so there exists q, 'IN q X' *)
pose (J:=lem3 S H X XinS).
destruct J as [b binX].
pose (binUS := IN_Union S X b XinS binX).
exists (in2term _ _ binUS).
fold X in XinS |- *.
simpl.
eapply IN_sound_left.
apply goodlem.
assumption.
Defined.

(* function and property *)
Definition fp := ex2sig _ _ (AC A B P hyp).
Definition fu := fun v : pi1 S =>
 OrdPair (pi2 S v) (pi2 (Union S) ((proj1_sig fp) v)).
Definition chfu : Ens := (sup (pi1 S) fu).
Theorem choifunc_total (X:Ens) (G:IN X S): exists Q, IN (OrdPair X Q) chfu /\ IN Q X.
Proof.
pose (t:=in2term S X G).
pose (p:=fu t).
(*&pose (p:=t). *)
unfold fu in p.
exists (pi2 (Union S) (proj1_sig fp t)).
split.
(*exists p.*)
{ unfold chfu.
  unfold IN.
exists t. (*!*)
unfold t.

apply OrdPair_sound_both.
apply goodlem.
apply EQ_refl. }
{ 
pose (Y:= proj2_sig fp t).
unfold P in Y.
eapply IN_sound_right.
2 : exact Y.
unfold t.
apply EQ_sym.
apply goodlem. }
Defined.
