
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

----------------

   destruct (lem3 S H X G) as [b binX].
  exists b.
  unfold Achfu.
  eapply IN_P_Comp.
   (*chfu*)
  
(*XinS
unfold PP in B.
simpl in *|-*.*)
Abort.


-------------


Theorem axChoice0 : forall S:Ens,
(~IN Vide S) -> exists f:Ens,
forall X, IN X S <-> 
((exists Q, IN (OrdPair X Q) f)/\
 (forall Q1 Q2, IN (OrdPair X Q1) f /\ IN (OrdPair X Q2) f -> EQ Q1 Q2)).
Proof.
intros.
pose (A:=(pi1 S)).
pose (B:=(pi1 (Union S))).
Check pi2.
pose (P:= fun (a:A) (b:B) => (*(IN (pi2 S a) S) /\ *)
(IN (pi2 (Union S) b) (pi2 S a))).
Check AC A B P.
assert (forall a : A, (exists b : B, P a b)).
{
 intro a.
 unfold P.
 pose (zz := lem3 S H (pi2 S a) (lem4 S a)).
 destruct zz as [v k].
 Check lem4 (Union S). 
 assert (b_aim : pi1 (pi2 S a)).
 { unfold IN in k.
   destruct (pi2 S a).
   admit.
 }
(* exists b_aim.
 exact (lem4 (Union S) b_aim).
 exists v.

IN (pi2 S a) S

 unfold A in a.

Check sup.
unfold pi1, pi2.*)
Lemma ac_lem (S:Ens) (H1:~EQ Vide S) (H2:~IN Vide S)
: exists e:Ens, IN e (Union S).
Proof.
apply not_all_not_ex.
intros B1.
Search Vide.
apply tout_vide_est_Vide in B1.
apply H1.
rewrite axExt.
rewrite axExt in B1.
intro w.
split; intro u.
+ destruct (Vide_est_vide w u).
+ apply B1.
Abort.
Abort.

--------------------------------------
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
