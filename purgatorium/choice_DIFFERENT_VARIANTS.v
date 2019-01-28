Definition P1:= fun ts tus => IN (pi2 (Union S) tus) (pi2 S ts).
Theorem hyp1 : forall a : A, (exists b : B, P1 a b).
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

unfold fp in R1,R2.
EQ
fp
unfold IN in K1.
destruct chfu. 
simpl  in * |- *.



unfold fu in p.

apply fu in t.

apply goodlem.
replace (exists y : A, EQ E1 (f y)).

simpl.

apply EQ_sym.
End easy.
(*
Inductive indA := 
| cindA (q:Ens) (J:IN q S): indA.
Inductive indB := 
| cindB (q:Ens) (J:IN q (Union S)): indB.
*)
Definition indA := { q:Ens | IN q S}.
Definition indB := { q:Ens | IN q (Union S)}.
Definition PP (iA:indA) (iB:indB) : Prop.
Proof.
destruct iA as [q J], iB as [q0 J0].
exact (IN q0 q).
Defined.
(*(forall a : A, exists b : B, P a b)*)
Theorem hyp1 : forall a : indA, exists b : indB, PP a b.
Proof. intro a. destruct a as [q J].
pose (W:=lem3 S H q J).
destruct W as [bb KK].
pose (LL:= IN_Union S q bb J KK).
exists (exist _ bb LL).
simpl.
exact KK.
Defined.

Definition mn : exists f : indA -> indB, forall a : indA, PP a (f a) 
 := AC indA indB PP hyp1.

Definition mnsig : {x : indA -> indB | forall a : indA, PP a (x a)}
 := (ex2sig _ _ mn).

Definition fiAtoiB : indA -> indB := proj1_sig mnsig.

Definition fiAtoiB_prop
     : forall a : indA,
       PP a (fiAtoiB a)
 := proj2_sig mnsig.

(*Definition fiAtoiB_prop
     : forall a : indA,
       PP a
         (proj1_sig
            (ex2sig (indA -> indB)
               (fun f : indA -> indB =>
                forall a0 : indA, PP a0 (f a0)) mn) a)
 := proj2_sig (ex2sig _ _ mn).*)
(*
Definition fiAtoiB' : indA -> indB.
Proof.
destruct (ex2sig _ _ mn) as [a B].
exact a.
Defined.

Definition fiAtoiB_prop' : forall a : indA, PP a (fiAtoiB a).
Proof.
destruct (ex2sig _ _ mn) as [a B].
try exact B.
Abort.*)

(* Definition of a choice function *)
(*Definition chfu : Ens.
Proof.
unshelve eapply (Comp (Product S (Union S)) _ ).
intro pa.
refine (exists l1 l2, EQ pa (OrdPair l1 l2) /\ _).
Abort.*)

Definition f0: (pi1 S) -> indA.
Proof. intro ts.
unshelve eapply exist.
exact (pi2 S ts).
apply lem4.
Defined.

(*Check (sup indA).*)
Check proj1_sig mnsig.
Definition fu:(pi1 S -> Ens).
Proof. intro ts.
pose (x:=(f0 ts)).
destruct (fiAtoiB x) as [v V].
exact (OrdPair (proj1_sig x) v).
Defined.

Definition choifunc : Ens := (sup (pi1 S) fu).

(*Definition chfu : Ens.
Proof.
(*destruct (ex2sig _ _ mn) as [a B].*)
(*apply ex2sig in mn.
destruct mn as [a B].*)
pose (ff:=Comp (Product S (Union S)) 
(fun pa=>
 exists l1 l2, EQ pa (OrdPair l1 l2) /\
  exists (g: IN l1 S),
match (fiAtoiB (cindA l1 g)) with
cindB q qinUS => EQ l2 q
end
)).
exact ff.
Defined.*)

Section sec3.
Context (X:Ens) (G:IN X S).
Definition XG : {q : Ens | IN q S} 
 := (exist (fun q : Ens => IN q S) X G).

Theorem choifunc_total : exists Q, IN (OrdPair X Q) choifunc.
Proof.
assert (F:indA).
{ unshelve eapply exist. exact X. exact G. }
Show Proof.
apply fiAtoiB in F as M.

(*destruct F as [f p].*)
exists (proj1_sig XG).
unfold choifunc.
unfold IN.
apply in2term in G as G1.
exists G1.
unfold fu.
destruct (fiAtoiB (f0 G1)).
unfold IN in G.
simpl.
change.
unshelve eapply exist.
fu IN
Theorem lem5 (S:Ens) (a:pi1 S) : IN (pi2 S a) S.
Proof.
induction S.
simpl.
exists a.
apply EQ_refl.
Defined.

exists (proj1_sig (exist (fun q : Ens => IN q S) X G)).
simpl.
eapply lem4.
simpl.
exists (pi2 S X).

simpl.

destruct choifunc.
destruct (proj1_sig mnsig (exist _ X _)) as [b B].
exist 
Defined.
(*Theorem chfu_total : exists Q, IN (OrdPair X Q) chfu.
Proof.
  destruct (lem3 S H X G) as [b binX].
  exists b.
  unfold chfu.
  eapply IN_P_Comp.
  { (* lem of soundness *) admit. }
  { (* trivial Search Product. Need Product_IN *) admit. }
  { exists X, b. split. apply EQ_refl. exists G. 
    induction (fiAtoiB (cindA X G)).
Abort.*)
End sec3.