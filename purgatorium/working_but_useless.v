
Definition Pi2_C (A B:Ens) : class.
Proof.
apply (Build_class' (Pi2_P (OrdPair A B)) ).
intros.
eapply (Pi2_sound_lem1 _ a); assumption.
Defined.

(* (Pi2_sound_lem2 _ _ _ _)
Check (Build_class (Pi2_P (OrdPair A B)) ).
Search Comp.
*)

(* definitions for classes *)
(* DEPRECATED
Definition cPair (A B:class) : class.
Proof.
unshelve eapply Build_class'.
+ intro x. exact (cEQ x A \/ cEQ x B).
+ intros a b aeqb H.
  destruct H as [H1|H2].
  * left.
    unfold cEQ in *|-*.
    rewrite axExt in aeqb.
    intro z.
    symmetry.
    rewrite <- H1.
    exact (aeqb z).
  * right.
    unfold cEQ in *|-*.
    rewrite axExt in aeqb.
    intro z.
    symmetry.
    rewrite <- H2.
    exact (aeqb z).
Defined.
*)
(* DEPRECATED
Definition cPow (A:class) : class.
Proof.
unshelve eapply Build_class'.
+ intro x. exact (issubclass x A).
+ simpl. intros a b aeqb H.
  unfold issubclass in * |- *.
  intros x bx.
  apply axExtC in aeqb.
  unfold cEQ in aeqb.
  rewrite <- (aeqb x) in bx.
  apply (H x bx).
Defined.
*)
(* (A:Ens->Prop) is also fine. *)
(*Definition cUnion (A:class) : class.
Proof.
unshelve eapply Build_class.
+ intro x. exact (exists z : Ens, A z /\ IN x z).
+ apply two_sided. intros a b aeqb H.
  destruct H as [z [K1 K2]].
  exists z. split. exact K1.
  apply IN_sound_left with (E:=a); assumption.
Defined.*)

(*forall z : Ens, a z -> b z
exact (issubclass x A).
exact (cEQ x A \/ cEQ x B).
    unfold stro*)


-----------------------------
(*
Definition Build_class' : forall Vprty : Ens -> Prop,
       (forall a b : Ens, EQ a b -> Vprty a -> Vprty b) -> class.
Proof. intros.
unshelve eapply Build_class.
exact Vprty.
apply two_sided. exact H.
Defined.
*)

----------------------------
(* Existential quantification *)
(* Rename:
EXType  to  ex
EXTypei to  ex_intro
*)

(* Cartesian product in Type *)
(*Inductive prod_t (A B : Type) : Type :=
    pair_t : A -> B -> prod_t A B.*)
(* Rename:
prod_t  to  prod
pair    to  pair
*)


(* Recursive Definition of the extentional equality on sets *)
(* BEST
Fixpoint EQ (E1 E2: Ens) {struct E2}: Prop.
Proof.
destruct E1 as [A f].
destruct E2 as [B g].
apply and.
exact (forall x : A, exists y : B, EQ (f x) (g y)).
exact (forall y : B, exists x : A, EQ (f x) (g y)).
Show Proof.
Defined.
*)

(* Both "{struct E1}" and "{struct E2}" works good. *)


(* ===================================== *)
(* START OF THE WORKING BUT USELESS CODE *)
(* ===================================== *)

(*
'isas' is a constructive version of 'ias'.
*)
Record isas (C : class) := {
 dmn : Ens;
 eqvias: cEQ C dmn; (*forall w : Ens, c w <-> IN w dmn;*)
}.


Theorem jhkl (x:Ens) (A:class) (H:cEQ A x): isas A.
Proof.
unshelve eapply Build_isas.
exact x. exact H.
Defined.

Theorem scosisas : forall (s : class) (m : Ens),
       (forall x : Ens, s x -> m x) -> isas s.
Proof. intros s m sc.
unshelve eapply Build_isas.
exact (Comp m s).
intro w.
split.
+ intro u.
  pose(y:=sc w u).
  (*unfold esiacf in * |- *.*)
  apply IN_P_Comp.
  * intros w1 w2 K H.
    rewrite <- (sound' s). exact K. exact H. (*apply (rewr _ _  K H).*)
  * exact y.
  * exact u.
+ intro u.
  apply (IN_Comp_P m).
  apply sound2rewr.
  exact u.
Defined.

(* strange proofs ... *)
Lemma cIN_sound_right' (A:class) (D k:Ens): A k -> cEQ A D -> IN k D.
Proof.
intros H K. unfold cEQ in K. apply K in H. simpl in H. exact H.
Defined.

Lemma cIN_sound_iff (A:class) (D k:Ens) (K:cEQ A D): A k <-> IN k D.
Proof.
split; intros H; 
apply K in H; (*simpl in H;*) exact H. (*twice*)
Defined.

Definition decid (A:Type) := sum A (A->False).

Record xclass := {
 clprj :> class;
 ciset :  decid (isas clprj);
}.

Definition xPair (A B:xclass) : xclass.
Proof.
ueapp Build_xclass.
exact (cPair (clprj A) (clprj B)).
left.
destruct (ciset A) as [ASE|APC], (ciset B) as [BSE|BPC].
+ unshelve eapply Build_isas.
  exact (Paire (dmn _ ASE) (dmn _ BSE)).
  intro z; split; intro x.
  - simpl in x. destruct x as [HA|HB].
    * simpl.
      change _ with (IN z (Paire (dmn A ASE) (dmn B BSE))).
      exists true; simpl.
      apply axExtC.
      intro k; split; intro m.
  ++ simpl. simpl in m.
     apply (HA k) in m.
     eapply (eqvias A ASE ). exact m.
     (* eapply cIN_sound_right. exact m. 
     exact (eqvias A ASE).*)
  ++ simpl. simpl in m.
     apply (HA k). eapply (eqvias A ASE ) in m. assumption.
    * simpl.
      change _ with (IN z (Paire (dmn A ASE) (dmn B BSE))).
      exists false; simpl.
      apply axExtC.
      intro k; split; intro m.
  ++ simpl. simpl in m.
     apply (HB k) in m.
     eapply (eqvias B BSE ). exact m.
     (* eapply cIN_sound_right. exact m. 
     exact (eqvias A ASE).*)
  ++ simpl. simpl in m.
     apply (HB k). eapply (eqvias B BSE ) in m. assumption.
  - simpl in * |- *.
    destruct x as [m J].
    destruct m; simpl in J.
    * left. apply axExtC in J.
(*    eapply cEQ_tran.
      apply J.
      intros a. split; intro h.
simpl in h.
simpl.*)
Abort.
(* END OF THE WORKING BUT USELESS CODE *)