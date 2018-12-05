(*** Contents ***
Part I: Large part of "/coq-contribs/zfc/" library and
proofs of some axioms of zfc.
Part II: Development of the classical ZFC theory with
 exercises from Jech's "Set theory". (try to avoid classes)
and "Introduction t set theory" books.
Part III: Development of formulas and derivations.
Part IV: Experiments with definions of a classes
and other experiments.
*****************)

(* IMPORTANT: during the development of the part II 
all definitions must be considered as unsafe.
Correctness is not bult-in due to apearing of
the big amount of bureaucracy. See part IV.
*)

(* AIMS:
 The first aim is to create a self-contained book 
of the first-order logic and ZFC set theory.
 The second aim is to solve exercises from Jech's "Set theory".
*)

(* These notions should not be unfolded:
Pair, Union, Powerset. *)


(* We will not import all that is in /zfc/ library.

From ZFC Require Import 
 Axioms
 Hierarchy
 Plump
 Sets
 Cartesian
 Omega
 Replacement
 (*zfc*)
 Constructive
 Ordinal_theory
 Russell
.

*)

Require Classical_Prop Classical_Pred_Type.
(*From ZFC Require Import Sets Axioms. (* Cartesian Omega.*)*)

(*============================================
                     Part I
==============================================*)

(* Remastered SETS.v *)

(* The type representing sets  (Ensemble = french for set) *)

Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.

(* Existential quantification *)
Check ex.
(* Rename:
EXType  to  ex
EXTypei to  ex_intro
*)
Inductive EXType (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei : forall x : P, Q x -> EXType P Q.


(* Cartesian product in Type *)

Inductive prod_t (A B : Type) : Type :=
    pair_t : A -> B -> prod_t A B.


(* Existential on the Type level *)

Inductive depprod (A : Type) (P : A -> Type) : Type :=
    dep_i : forall x : A, P x -> depprod A P.


(* Recursive Definition of the extentional equality on sets *)

Definition EQ : Ens -> Ens -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType _ (fun x : A => eq1 x (g y))).
Defined.

(* Membership on sets *)

Definition IN (E1 E2 : Ens) : Prop :=
  match E2 with
  | sup A f => EXType _ (fun y : A => EQ E1 (f y))
  end.


(* INCLUSION *)

Definition INC : Ens -> Ens -> Prop.
intros E1 E2.
exact (forall E : Ens, IN E E1 -> IN E E2).
Defined.



(* EQ is an equivalence relation  *)

Theorem EQ_refl : forall E : Ens, EQ E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto.

exists y; auto.
Defined.

Theorem EQ_tran : forall E1 E2 E3 : Ens, EQ E1 E2 -> EQ E2 E3 -> EQ E1 E3.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2;
 simple induction E3; intros A3 f3 r3; simpl in |- *; 
 intros e1 e2.
split; (elim e1; intros I1 I2; elim e2; intros I3 I4).
intros a1; elim (I1 a1); intros a2.
elim (I3 a2); intros a3.
exists a3.
apply r1 with (f2 a2); auto.
intros a3; elim (I4 a3); intros a2; elim (I2 a2); intros a1; exists a1.
apply r1 with (f2 a2); auto.
Defined.

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2;
 simpl in |- *; simple induction 1; intros e1 e2; split.
intros a2; elim (e2 a2); intros a1 H1; exists a1; auto.
intros a1; elim (e1 a1); intros a2 H2; exists a2; auto.
Defined.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 simpl in |- *; simple induction 1; intros e1 e2; unfold INC in |- *;
 simpl in |- *.
intros C; simple induction 1; intros a ea; elim (e1 a); intros a' ea';
 exists a'.
apply EQ_tran with (f a); assumption.
Defined.

Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.

(* easy lemma *)

Theorem INC_EQ : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 unfold INC in |- *; simpl in |- *; intros I1 I2; split.
intros a; apply I1.
exists a; auto with zfc.
intros a'; cut (EXType A (fun x : A => EQ (f' a') (f x))).
simple induction 1; intros a ea; exists a; auto with zfc.
apply I2; exists a'; auto with zfc.
Defined.

Hint Resolve INC_EQ: zfc.


(* Membership is extentional (i.e. is stable w.r.t. EQ)   *)

Theorem IN_sound_left :
 forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
simple induction E''; intros A'' f'' r'' e; simpl in |- *; simple induction 1;
 intros a'' p; exists a''; apply EQ_tran with E; auto with zfc.
Defined.

Theorem IN_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
simple induction E'; intros A' f' r'; simple induction E'';
 intros A'' f'' r''; simpl in |- *; simple induction 1; 
 intros e1 e2; simple induction 1; intros a' e'; elim (e1 a'); 
 intros a'' e''; exists a''; apply EQ_tran with (f' a'); 
 assumption.

Defined.

(* Inclusion is reflexive, transitive, extentional *)

Theorem INC_refl : forall E : Ens, INC E E.
unfold INC in |- *; auto with zfc.
Defined.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
unfold INC in |- *; auto with zfc.
Defined.


Theorem INC_sound_left :
 forall E E' E'' : Ens, EQ E E' -> INC E E'' -> INC E' E''.
simple induction E''; unfold INC in |- *; simpl in |- *;
 intros A f HR e H1 E0 i; apply H1.
apply IN_sound_right with E'; auto with zfc.
Defined.

Theorem INC_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> INC E E' -> INC E E''.
simple induction E'; simple induction E''; unfold INC in |- *; simpl in |- *;
 intros.
elim (H2 E0); try assumption; intros.
elim H1; intros HA HB; elim (HA x); intros.
exists x0; apply EQ_tran with (e x); auto with zfc.
Defined.


(* page 3 *)
Theorem axExt : forall x y : Ens,
   EQ x y <-> forall z, (IN z x <-> IN z y).
Proof.
intros.
split.
+ intros.
  split.
  - apply IN_sound_right. exact H.
  - apply IN_sound_right. apply EQ_sym. exact H.
+ induction x as [A f], y as [B g].
  intro K.
  simpl in * |- *.
  split.
  - intro x.
    apply K.
    exists x.
    apply EQ_refl.
  - intro y.
    assert (Q:EXType B (fun y0 : B => EQ (g y) (g y0))).
    * exists y.
      apply EQ_refl.
    * destruct (proj2 (K (g y)) Q).
      exists x.
      apply EQ_sym.
      exact H0.
Defined.

(************ Remastered Axioms.v ***************)

(* Definitions of the empty set, pair, union, intersection, comprehension  *)
(*  axiom and powerset, together with their properties                     *)

(* Useful types (actually top and bottom)   *)

Inductive Un : Set :=
    void : Un.

Inductive F : Set :=.

(* The empty set  (vide = french for empty)   *)

Definition Vide : Ens := sup F (fun f : F => match f return Ens with
                                             end).

(* The axioms of the empty set *)

Theorem Vide_est_vide : forall E : Ens, IN E Vide -> F.
unfold Vide in |- *; simpl in |- *; intros E H; cut False.
simple induction 1.
elim H; intros x; elim x.
Defined.


Theorem tout_vide_est_Vide :
 forall E : Ens, (forall E' : Ens, IN E' E -> F) -> EQ E Vide.
 unfold Vide in |- *; simple induction E; simpl in |- *; intros A e H H0;
  split.
intros; elim (H0 (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.
Defined.

(* Pair *)

Definition Paire : forall E E' : Ens, Ens.
intros.
apply (sup bool).
simple induction 1.
exact E.
exact E'.
Defined.

(* The pair construction is extentional *)

Theorem Paire_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Paire A B) (Paire A' B).
unfold Paire in |- *.
simpl in |- *.
intros; split.
simple induction x.
exists true; auto with zfc.

exists false; auto with zfc.

simple induction y; simpl in |- *.
exists true; auto with zfc.

exists false; auto with zfc.
Defined.

Theorem Paire_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Paire A B) (Paire A B').
unfold Paire in |- *; simpl in |- *; intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y.
exists true; auto with zfc.
exists false; auto with zfc.
Defined.

Hint Resolve Paire_sound_right Paire_sound_left: zfc.

(* The axioms of the pair *)

Theorem IN_Paire_left : forall E E' : Ens, IN E (Paire E E').
unfold Paire in |- *; simpl in |- *; exists true; simpl in |- *;
 auto with zfc.
Defined.

Theorem IN_Paire_right : forall E E' : Ens, IN E' (Paire E E').
unfold Paire in |- *; simpl in |- *; exists false; simpl in |- *;
 auto with zfc.
Defined.

Theorem Paire_IN :
 forall E E' A : Ens, IN A (Paire E E') -> EQ A E \/ EQ A E'.
unfold Paire in |- *; simpl in |- *.
simple induction 1; intros b; elim b; simpl in |- *; auto with zfc.
Defined.

Hint Resolve IN_Paire_left IN_Paire_right Vide_est_vide: zfc.

(* The singleton set  *)
(* Note that we could define it directly using the base type Un *)

Definition Sing (E : Ens) := Paire E E.


(* The axioms  *)

Theorem IN_Sing : forall E : Ens, IN E (Sing E).
unfold Sing in |- *; auto with zfc.
Defined.

Theorem IN_Sing_EQ : forall E E' : Ens, IN E (Sing E') -> EQ E E'.
unfold Sing in |- *; intros E E' H; elim (Paire_IN E' E' E);
 auto with zfc.
Defined.



Hint Resolve IN_Sing IN_Sing_EQ: zfc.

Theorem Sing_sound : forall A A' : Ens, EQ A A' -> EQ (Sing A) (Sing A').
unfold Sing in |- *; intros; apply EQ_tran with (Paire A A');
 auto with zfc.
Defined.

Hint Resolve Sing_sound: zfc.

Theorem EQ_Sing_EQ : forall E1 E2 : Ens, EQ (Sing E1) (Sing E2) -> EQ E1 E2.
intros; cut (IN E1 (Sing E2)).
intros; auto with zfc.
apply IN_sound_right with (Sing E1); auto with zfc.
Defined.

Hint Resolve EQ_Sing_EQ: zfc.



(* We here need sigma types -- i.e. computational existentials *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig A P.


(* The set obtained by the comprehension (or separation) axiom *)

Definition Comp : Ens -> (Ens -> Prop) -> Ens.
simple induction 1; intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
simple induction 1; intros x p; exact (f x).
Defined.

(* The comprehension/separation axioms *)

Theorem Comp_INC : forall (E : Ens) (P : Ens -> Prop), INC (Comp E P) E.
unfold Comp, INC in |- *; simple induction E; simpl in |- *; intros.
elim H0; simple induction x; intros; exists x0; auto with zfc.
Defined.

Theorem IN_Comp_P :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) -> IN A (Comp E P) -> P A.
simple induction E; simpl in |- *; intros B f Hr A P H i; elim i; intros c;
 elim c; simpl in |- *; intros x q e; apply H with (f x); 
 auto with zfc.
Defined.

Theorem IN_P_Comp :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) ->
 IN A E -> P A -> IN A (Comp E P).
simple induction E; simpl in |- *; intros B f HR A P H i; elim i;
 simpl in |- *; intros.
cut (P (f x)).
intros Pf.
exists (exist B (fun x : B => P (f x)) x Pf); simpl in |- *;
 auto with zfc.
apply H with A; auto with zfc.
Defined.

(* Again, extentionality is not stated, but easy *)


(* Projections of a set: *)
(*  1: its base type     *)

Definition pi1 : Ens -> Type.
simple induction 1.
intros A f r.
exact A.
Defined.

(*  2: the function      *)

Definition pi2 : forall E : Ens, pi1 E -> Ens.
simple induction E.
intros A f r.
exact f.
Defined.

(* The Union set   *)

Definition Union : forall E : Ens, Ens.
simple induction 1; intros A f r.
apply (sup (depprod A (fun x : A => pi1 (f x)))).
simple induction 1; intros a b.
exact (pi2 (f a) b).
Defined.

Theorem EQ_EXType :
 forall E E' : Ens,
 EQ E E' ->
 forall a : pi1 E,
 EXType (pi1 E') (fun b : pi1 E' => EQ (pi2 E a) (pi2 E' b)).
simple induction E; intros A f r; simple induction E'; intros A' f' r';
 simpl in |- *; simple induction 1; intros e1 e2 a.
apply e1.
Defined.

Theorem IN_EXType :
 forall E E' : Ens,
 IN E' E -> EXType (pi1 E) (fun a : pi1 E => EQ E' (pi2 E a)).
simple induction E; simpl in |- *.
intros A f r.
simple induction 1; simpl in |- *.
intros.
exists x; auto with zfc.
Defined.

(* The union axioms *)
Theorem IN_Union :
 forall E E' E'' : Ens, IN E' E -> IN E'' E' -> IN E'' (Union E).

simple induction E; intros A f r.
intros.
simpl in |- *.
elim (IN_EXType (sup A f) E' H).
intros x e.
cut (EQ (pi2 (sup A f) x) E'); auto with zfc.
intros e1.
cut (IN E'' (pi2 (sup A f) x)).
intros i1.
elim (IN_EXType _ _ i1).
intros x0 e2.
simpl in x0.
exists (dep_i A (fun x : A => pi1 (f x)) x x0).
simpl in |- *.
exact e2.
apply IN_sound_right with E'; auto with zfc.
Defined.


Theorem IN_INC_Union : forall E E' : Ens, IN E' E -> INC E' (Union E).
unfold INC in |- *; simple induction E; intros A f r; unfold Union in |- *.
intros E' i E'' i'; simpl in |- *; elim (IN_EXType (sup A f) E' i).
intros a e; simpl in a; simpl in e.
elim (IN_EXType E' E'' i').
cut (IN E'' (f a)).
intros i'' a' e''; elim (IN_EXType _ _ i''); simpl in |- *; intros aa ee.
exists (dep_i A (fun x : A => pi1 (f x)) a aa); auto with zfc.
apply IN_sound_right with E'; auto with zfc.
Defined.

Theorem Union_IN :
 forall E E' : Ens,
 IN E' (Union E) -> EXType _ (fun E1 : Ens => IN E1 E /\ IN E' E1).
simple induction E; unfold Union in |- *; simpl in |- *; intros A f r.
simple induction 1.
simple induction x.
intros a b; simpl in |- *.
intros.
exists (f a).
split.
exists a; auto with zfc.

apply IN_sound_left with (pi2 (f a) b); auto with zfc.
simpl in |- *.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
Defined.


(* extentionality of union  *)

Theorem Union_sound : forall E E' : Ens, EQ E E' -> EQ (Union E) (Union E').
unfold Union in |- *; simple induction E; intros A f r; simple induction E';
 intros A' f' r'; simpl in |- *; simple induction 1; 
 intros e1 e2; split.
intros x; elim x; intros a aa; elim (e1 a); intros a' ea.
elim (EQ_EXType (f a) (f' a') ea aa); intros aa' eaa.
exists (dep_i A' (fun x : A' => pi1 (f' x)) a' aa'); simpl in |- *;
 auto with zfc.
intros c'; elim c'; intros a' aa'; elim (e2 a'); intros a ea.
cut (EQ (f' a') (f a)).
2: auto with zfc.
intros ea'; elim (EQ_EXType (f' a') (f a) ea' aa'); intros aa eaa.
exists (dep_i A (fun x : A => pi1 (f x)) a aa); auto with zfc.

Defined.



(* The union construction is monotone w.r.t. inclusion   *)

Theorem Union_mon : forall E E' : Ens, INC E E' -> INC (Union E) (Union E').
unfold INC in |- *; intros E E' IEE E'' IEE''.
elim (Union_IN E E'').
intros E'''; simple induction 1; intros I1 I2.
apply IN_Union with E'''; auto with zfc.
auto with zfc.

Defined.

(* The  Intersection set   *)


Definition Inter (E : Ens) : Ens :=
  Comp (Union E) (fun e : Ens => forall a : Ens, IN a E -> IN e a).

Theorem IN_Inter_all :
 forall E E' : Ens,
 IN E' (Inter E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
unfold Inter in |- *.
intros E E' i.
change ((fun e : Ens => forall a : Ens, IN a E -> IN e a) E') in |- *.
apply (IN_Comp_P (Union E) E').
intros.
apply IN_sound_left with w1; auto with zfc.
assumption.
Defined.

Theorem all_IN_Inter :
 forall E E' E'' : Ens,
 IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter E).
unfold Inter in |- *.
intros.
apply IN_P_Comp.
intros; apply IN_sound_left with w1; auto with zfc.
apply IN_Union with (E' := E''); auto with zfc.
auto with zfc.
Defined.

(*  The powerset and its axioms   *)

Definition Power (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun P : A -> Prop =>
         sup _
           (fun c : depprod A (fun a : A => P a) =>
            match c with
            | dep_i _ _ a p => f a
            end))
  end.


Theorem IN_Power_INC : forall E E' : Ens, IN E' (Power E) -> INC E' E.
simple induction E.
intros A f r; unfold INC in |- *; simpl in |- *.
intros E'; simple induction 1; intros P.
elim E'; simpl in |- *.
intros A' f' r'.
simple induction 1; intros HA HB.
intros E''; simple induction 1; intros a' e.
elim (HA a').
simple induction x; intros a p.
intros; exists a.
auto with zfc.
apply EQ_tran with (f' a'); auto with zfc.
Defined.



Theorem INC_IN_Power : forall E E' : Ens, INC E' E -> IN E' (Power E).
simple induction E; intros A f r; unfold INC in |- *; simpl in |- *.
simple induction E'; intros A' f' r' i.
exists (fun a : A => IN (f a) (sup A' f')).
simpl in |- *.
split.
intros.
elim (i (f' x)); auto with zfc.
intros a e.
cut (EQ (f a) (f' x)); auto with zfc.
intros e1.
exists
 (dep_i A (fun a : A => EXType A' (fun y : A' => EQ (f a) (f' y))) a
    (EXTypei A' (fun y : A' => EQ (f a) (f' y)) x e1)).
simpl in |- *.
auto with zfc.

auto with zfc.
simpl in |- *.
exists x; auto with zfc.

simple induction y; simpl in |- *.
simple induction 1; intros.
exists x0; auto with zfc.
Defined.

Theorem Power_mon : forall E E' : Ens, INC E E' -> INC (Power E) (Power E').
intros.
unfold INC in |- *; intros.
apply INC_IN_Power.
cut (INC E0 E).
unfold INC in |- *; unfold INC in H; intros; auto with zfc.
apply IN_Power_INC; auto with zfc.
Defined.

Theorem Power_sound : forall E E' : Ens, EQ E E' -> EQ (Power E) (Power E').
intros E E' e.
apply INC_EQ; unfold INC in |- *.
intros A i.
cut (INC A E').
intros; apply INC_IN_Power; assumption.
cut (INC A E); intros.
apply INC_sound_right with E; auto with zfc.
apply IN_Power_INC; assumption.
intros A i.
cut (INC A E).
intros; apply INC_IN_Power; assumption.
cut (INC A E'); intros.
apply INC_sound_right with E'; auto with zfc.
apply IN_Power_INC; assumption.
Defined.





(* small lemma *)

Theorem not_EQ_Sing_Vide : forall E : Ens, EQ (Sing E) Vide -> F.
intros E e; cut False.
simple induction 1.
cut (IN E Vide).
simpl in |- *; simple induction 1; intros xx; elim xx; simple induction 1.
apply IN_sound_right with (Sing E); auto with zfc.
Defined.


Theorem not_EQ_Vide_Sing : forall E : Ens, EQ Vide (Sing E) -> F.
intros E e; cut False.
simple induction 1.
cut (IN E Vide).
simpl in |- *; simple induction 1; intros xx; elim xx; simple induction 1.
apply IN_sound_right with (Sing E); auto with zfc.
Defined.


(*============================================
                     Part II
==============================================*)

(* Traditional Product needs Kuratowski ordered pair *)

(* Kuratowski construction *)
Definition OrdPair (x y : Ens) := Paire (Sing x) (Paire x y).

Theorem OrdPair_sound_left (x1 x2 y : Ens) (H : EQ x1 x2)
 : EQ (OrdPair x1 y) (OrdPair x2 y).
Proof.
unfold OrdPair.
apply EQ_tran with (E2:=Paire (Sing x1) (Paire x2 y)).
+ eapply Paire_sound_right.
  eapply Paire_sound_left.
  assumption.
+ eapply Paire_sound_left.
  eapply Sing_sound.
  assumption.
Defined.

Theorem OrdPair_sound_right (x y1 y2 : Ens) (H : EQ y1 y2)
 : EQ (OrdPair x y1) (OrdPair x y2).
Proof.
unfold OrdPair.
eapply Paire_sound_right.
eapply Paire_sound_right.
assumption.
Defined.

Lemma SingEqPair x y1 y2 (J: EQ (Sing x) (Paire y1 y2)) :
EQ x y1 /\ EQ x y2.
Proof.
apply EQ_sym in J.
pose (i1:=IN_Paire_left y1 y2).
apply IN_sound_right with (1:=J) in i1.
apply IN_Sing_EQ, EQ_sym in i1.
pose (i2:=IN_Paire_right y1 y2).
apply IN_sound_right with (1:=J) in i2.
apply IN_Sing_EQ, EQ_sym in i2.
split; assumption.
Defined.

Lemma Paire_sound (a b c d:Ens) (L:EQ a c) (R:EQ b d) 
 : EQ (Paire a b) (Paire c d).
Proof.
  apply EQ_tran with (E2:= Paire a d).
  apply Paire_sound_right, R.
  apply Paire_sound_left, L.
Defined.

Lemma Paire_EQ_cases a b c d (H:EQ (Paire a b) (Paire c d)) : 
(EQ a c \/ EQ a d)/\(EQ b c \/ EQ b d).
Proof.
rewrite axExt in H.
split.
+ destruct (H a) as [W1 _].
  assert (E := W1 (IN_Paire_left a b)).
  apply Paire_IN. assumption.
+ destruct (H b) as [W1 _].
  assert (E := W1 (IN_Paire_right a b)).
  apply Paire_IN. assumption.
Defined.

Theorem OrdPair_inj : forall a b c d : Ens, 
  EQ (OrdPair a b) (OrdPair c d)->(EQ a c/\EQ b d).
Proof. 
unfold OrdPair in |- *. intros.
pose (H1:=H).
apply Paire_EQ_cases in H1 as [K1 K2].
split.
 destruct K1 as [A|B].
  apply EQ_Sing_EQ. assumption.
  apply SingEqPair in B as [n1 n2]. assumption.

 destruct K1 as [A|B], K2 as [C|D].
 (*as [[A|B] [C|D]].*)
+ (*split. apply EQ_Sing_EQ. assumption.*)
  apply EQ_sym in C.
  apply SingEqPair in C as [J1 J2].
  assert(i: EQ (Paire (Sing a) (Paire a b))
                (Sing (Sing a) )).
   apply Paire_sound_right.
   apply Paire_sound_right.
   apply EQ_sym in J2.
   eapply EQ_tran with (E2:=c); assumption.
  apply EQ_sym, EQ_tran with (2:=H) in i.
  apply SingEqPair in i as [F1 F2].
  apply SingEqPair in F2 as [U1 U2].
  eapply EQ_tran. apply EQ_sym. exact J2.
  eapply EQ_tran. apply EQ_sym. exact U1.
  exact U2.
+ pose (i:=IN_Paire_right c d).
  eapply IN_sound_right in i.
  2 : { apply EQ_sym, D. }
  apply Paire_IN in i as [X1|X2].
  2 : { apply EQ_sym, X2. }
  pose (y:=IN_Paire_right a b).
  eapply IN_sound_right in y.
  2 : { apply D. }
  apply Paire_IN in y as [Y1|Y2].
   apply EQ_Sing_EQ in A.
   apply EQ_tran with (E2:=c). assumption.
   apply EQ_sym, EQ_tran with (E2:=a); assumption.
  assumption.
+ apply EQ_sym, SingEqPair in C as [F1 F2].
  apply SingEqPair in B as [P1 P2].
  apply EQ_tran with (E2:=c). apply EQ_sym; exact F2.
  apply EQ_tran with (E2:=a). apply EQ_sym; exact P1.
  exact P2.
+ pose (i:=IN_Paire_right c d).
  eapply IN_sound_right in i.
  2 : { apply EQ_sym, D. }
  apply Paire_IN in i as [X1|X2].
  2 : { apply EQ_sym, X2. }
  assert (v:EQ (Sing a) (Paire a b)).
   apply EQ_sym in D.
   apply EQ_tran with (1:=B). assumption.
  apply SingEqPair in v as [U1 U2].
  apply EQ_sym.
  apply (EQ_tran d a b X1 U2).
Defined.

Theorem OrdPair_inj_right :
 forall A A' B B' : Ens, EQ (OrdPair A A') (OrdPair B B') -> EQ A' B'.
Proof.
intros. apply OrdPair_inj in H as [a b]. exact b.
Defined.

(* predicate for separation of the product *)

(*Definition cProduct (X Y : class) : class.
Proof.
unshelve eapply Build_class.
intro z.
exact (exists (x y:Ens), (EQ z (OrdPair x y)) /\ X x /\ Y y).
apply sousym.
intros a b aeqb e.
destruct e as [x [y [aeq [xx yy]]]].
exists x, y.
repeat split.
{ apply EQ_tran with (E2:=a).
  apply EQ_sym. exact aeqb.
  exact aeq. }
exact xx.
exact yy.
Defined.*)

Definition inSProduct (X Y z:Ens) :=
(exists (x y:Ens), (EQ z (OrdPair x y)) /\ IN x X /\ IN y Y).

(* Product of sets *)
Definition SProduct (X Y:Ens) :=
Comp
 (Power (Power (Union (OrdPair X Y))))
 (inSProduct X Y)
.
(* you may prove: x is subset of *)

(*============================================
                     Part III
==============================================*)



(*============================================
                     Part IV
==============================================*)

(* TODO Определить операцию на классе и перенести её на множества. *)
(* Каждый класс, по определению, это некоторое свойство множеств. *)
(* Определение n-классов:
 0-класс - это множество.
 (n+1)-класс - это некоторое свойство n-классов.
*)

(* 'class' is the type of well-defined classes. *)
Record class := {
 prty :> Ens->Prop;
 sound : forall (a b : Ens), EQ a b -> (prty a <-> prty b);
}.

(*
Definition EQC (A B:class) := forall z:Ens, (prty A) z <-> (prty B) z.
*)
Definition EQC (A B: Ens->Prop) := forall z:Ens, A z <-> B z.

Lemma sousym (K:Ens->Prop)
(H:forall (a b : Ens), EQ a b -> (K a -> K b))
: forall (a b : Ens), EQ a b -> (K a <-> K b).
Proof.
intros a b aeqb. split.
apply (H a b aeqb).
apply H. apply EQ_sym. exact aeqb.
Defined.


(* set to class *)
Definition stoc : Ens -> class.
Proof.
intro x.
unshelve eapply Build_class.
+ intro y. exact (IN y x).
+ intros a b aeqb.
  apply sousym.
  intros a0 b0 H H0.
  eapply IN_sound_left. exact H. exact H0. exact aeqb.
  (*- apply IN_sound_left. apply EQ_sym. exact aeqb.*)
Defined.

Coercion stoc : Ens >-> class.

Definition axExtC (x y:Ens) : EQ x y <-> EQC x y
 := (axExt x y).

(* New comprehension *)
Definition Compr : Ens -> class -> Ens.
Proof.
intros e c.
exact (Comp e c).
Defined.

(*Definition nComp_sound_left x y C (H:EQ x y)
: EQ (Compr x C) (Compr y C).
Proof.
apply axExtC.
intro z. split.
+ intro a. simpl in * |- *.
  (*unfold Compr in * |- *. *)
 auto with zfc.*)


(* Product of classes *)
Definition cProduct (X Y : class) : class.
Proof.
unshelve eapply Build_class.
intro z.
exact (exists (x y:Ens), (EQ z (OrdPair x y)) /\ X x /\ Y y).
apply sousym.
intros a b aeqb e.
destruct e as [x [y [aeq [xx yy]]]].
exists x, y.
repeat split.
{ apply EQ_tran with (E2:=a).
  apply EQ_sym. exact aeqb.
  exact aeq. }
exact xx.
exact yy.
Defined.

(* Product of sets *)
Definition eProduct (x y:Ens) :=
Comp
 (Power (Power (Union (OrdPair x y))))
 (cProduct x y)
.

Definition issubclass (a b:class):Prop := forall z, a z -> b z.

Theorem pairisamemofpow (r1 r2 R:Ens) (H1 : IN r1 R) (H2 : IN r2 R)
 : IN (Paire r1 r2) (Power R).
Proof.
apply INC_IN_Power.
intros z H.
apply Paire_IN in H as [H|H];
 apply EQ_sym in H;
 apply IN_sound_left with (1:=H);
 assumption.
Defined.

(* Theorem thm (x a:Ens) : (prty (stoc x) a) = IN a x.
Proof. firstorder. Defined. *)

(* Product of sets as classes is a subclass of set. *)
Theorem prodissc: forall (X1 X2:Ens),
 issubclass
 (cProduct X1 X2)
 (Power (Power (Union (Paire X1 X2))))
.
Proof.
intros X1 X2 a H.
pose (H1 := H).
destruct H1 as [x1 [x2 [A [B1 B2]]]].
simpl in B1, B2.

pose (Q:=Power (Power (Union (Paire X1 X2)))).
fold Q.
change _ with (IN a Q).
apply INC_IN_Power.
intros s1 U1.
apply INC_IN_Power.
intros s2 U2.
apply IN_sound_right with (1:=A) in U1.
apply Paire_IN in U1 as [V1|V2].
+ apply IN_Union with (E':=X1).
  apply IN_Paire_left.
  apply IN_sound_right with (1:=V1) in U2.
  apply IN_Sing_EQ, EQ_sym in U2.
  apply IN_sound_left with (1:=U2), B1.
+ apply IN_sound_right with (1:=V2) in U2.
  apply Paire_IN in U2 as [c1|c2].
  - apply IN_Union with (E':=X1).
    apply IN_Paire_left.
    apply EQ_sym in c1.
    eapply IN_sound_left with (1:=c1).
    exact B1.
  - apply IN_Union with (E':=X2).
    apply IN_Paire_right.
    apply EQ_sym in c2.
    eapply IN_sound_left with (1:=c2).
    exact B2.
Defined.

(* Class of all sets *)
Definition cV : class.
Proof.
unshelve eapply Build_class.
+ intro z. exact True.
+ apply sousym. intros a b H1 H2. exact H2.
Defined.

(* Empty class *)
Definition cE : class.
Proof.
unshelve eapply Build_class.
+ intro z. exact False.
+ apply sousym. intros a b H1 H2. exact H2.
Defined.

(*_________________________________*)

(* (n+1)th power of A *)
Fixpoint cp1Pow (A:class) (n:nat) : class :=
match n with
 | O => A
 | S x => cProduct (cp1Pow A x) A 
end.

(* Relations *)

Definition cDom (R:class) : class.
Proof.
unshelve eapply Build_class.
intro u.
exact (exists v, R (OrdPair u v)).
apply sousym.
intros a b aeqb H.
destruct H as [x w].
exists x.
rewrite (sound R).
exact w.
apply OrdPair_sound_left.
auto with zfc. (*apply EQ_sym; exact aeqb.*)
Defined.

(* "is a set" predicate on classes *)
Definition ias (s: class) : Prop.
Proof.
exact (exists (x:Ens), forall w, s w <-> IN w x).
Defined.

(* "is a set" is a sound property on classes. *)
Definition ias_sound (A B: class)
(w:EQC A B) (H:ias A): ias B.
Proof.
unfold ias in * |- *.
destruct H as [x eqv].
exists x.
intro z.
unfold EQC in w.
rewrite <- w.
apply eqv.
Defined.

Definition exampleproperclass : class.
Proof.
Abort.

(*Definition ias (s: class) : Prop.*)
(* Proof. firstorder. (* Show Proof. *) . Defined. *)

Definition cprty_sound (cprty:class->Prop) (A B: class)
(w:EQC A B) (H:cprty A): cprty B.
Proof. unfold EQC in w. firstorder. (*impossible*) Abort.

(* ToDo: Find unsound class property. *)
Definition cprty_unsound : exists (cprty : class->Prop) 
(A B : class) (w : EQC A B) (HA : cprty A) (HB : cprty B), False.
Proof. Abort.

Lemma sound2rewr (s:class) : forall w1 w2 : Ens, s w1 -> EQ w1 w2 -> s w2.
Proof.
intros w1 w2 H1 H2. rewrite <- (sound s). exact H1. exact H2.
Defined.

(* subclass of a set is a set *)
Theorem scosias (s:class) (m:Ens) 
(sc : forall x, s x -> (stoc m) x) 
: ias s.
Proof.
unfold ias.
(*unfold  stoc in * |- *. esiacf*)
(* { x e. m | s x }*)
exists (Comp m s).
intro w.
split.
+ intro u.
  pose(y:=sc w u).
  (*unfold esiacf in * |- *.*)
  apply IN_P_Comp.
  * intros w1 w2 K H.
    rewrite <- (sound s). exact K. exact H. (*apply (rewr _ _  K H).*)
  * exact y.
  * exact u.
+ intro u.
  apply (IN_Comp_P m).
  apply sound2rewr.
  exact u.
Defined.
(* try the same proof through the powerset *)

(* Cartesian product of sets is a set. *)
Theorem cpss (x y : Ens) : ias (cProduct x y).
Proof.
eapply scosias.
intros z H.
apply prodissc.
exact H.
Defined.

(* Cartesian product as an operation on sets *)
Definition Product (x y:Ens): Ens.
Proof.
exact (Compr (Power (Power (Union (Paire x y)))) (cProduct x y)).
(* pose (w:=(cpss x y)). unfold ias in w.
   fails when destruct w. *)
Defined.

(* Now I will define extraction of the first and the 
second element of a couple. *)

Theorem unionsing (M : Ens) : EQ (Union (Sing M)) M.
Proof.
apply axExt.
intro z; split; intro y.
+ apply Union_IN in y.
  destruct y as [w [K1 K2]].
  apply IN_Sing_EQ in K1.
  apply IN_sound_right with (E':=w); assumption.
+ unshelve eapply IN_Union.
  exact M.
  exact (IN_Sing M).
  assumption.
Defined.

Theorem sing2union W M : EQ W (Sing M) -> EQ (Union W) M.
Proof. intro H. pose (y:= unionsing M).
apply EQ_tran with (E2:=Union (Sing M)).
apply Union_sound. assumption.
assumption.
Defined.

Theorem Comp_elim x y (K:class) : IN x (Comp y K) -> (IN x y /\ K x).
Proof.
intro e.
split.
+ exact ((Comp_INC y K) _ e).
+ apply IN_Comp_P in e. exact e.
  intros.
  rewrite <- (sound K).
  exact H.
  exact H0.
Defined.

(* definitions for classes *)
Definition cPair (A B:class) : class.
Proof.
unshelve eapply Build_class.
+ intro x. exact (EQC x A \/ EQC x B).
+ apply sousym.
  intros a b aeqb H.
  destruct H as [H1|H2].
  * left.
    unfold EQC in *|-*.
    rewrite axExt in aeqb.
    intro z.
    symmetry.
    rewrite <- H1.
    exact (aeqb z).
  * right.
    unfold EQC in *|-*.
    rewrite axExt in aeqb.
    intro z.
    symmetry.
    rewrite <- H2.
    exact (aeqb z).
Defined.

Definition cPow (A:class) : class.
Proof.
unshelve eapply Build_class.
+ intro x. exact (issubclass x A).
+ apply sousym. intros a b aeqb H.
  unfold issubclass in * |- *.
  intros x bx.
  apply axExtC in aeqb.
  unfold EQC in aeqb.
  rewrite <- (aeqb x) in bx.
  apply (H x bx).
Defined.

(* (A:Ens->Prop) is also fine. *)
Definition cUnion (A:class) : class.
Proof.
unshelve eapply Build_class.
+ intro x. exact (exists z : Ens, A z /\ IN x z).
+ apply sousym. intros a b aeqb H.
  destruct H as [z [K1 K2]].
  exists z. split. exact K1.
  apply IN_sound_left with (E:=a); assumption.
Defined.

(*forall z : Ens, a z -> b z
exact (issubclass x A).
exact (EQC x A \/ EQC x B).
    unfold stro*)

(*
'isas' is a constructive version of 'ias'.
*)
Record isas (C : class) := {
 dmn : Ens;
 eqvias: EQC C dmn; (*forall w : Ens, c w <-> IN w dmn;*)
}.

Definition decid (A:Type) := sum A (A->False).

Record xclass := {
 clprj :> class;
 ciset :  decid (isas clprj);
}.

Theorem jhkl (x:Ens) (A:class) (H:EQC A x): isas A.
Proof.
unshelve eapply Build_isas.
exact x. exact H.
Defined.
Check scosias.

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
    rewrite <- (sound s). exact K. exact H. (*apply (rewr _ _  K H).*)
  * exact y.
  * exact u.
+ intro u.
  apply (IN_Comp_P m).
  apply sound2rewr.
  exact u.
Defined.

Ltac ueapp P := unshelve eapply P.

Lemma EQC_refl (x:class): EQC x x.
Proof.
intros m; reflexivity.
Defined.

Lemma EQC_symm (x y:class): EQC x y -> EQC y x.
Proof.
intros H m. symmetry. apply H.
Defined.

Lemma EQC_tran (x y z:class): EQC x y -> EQC y z -> EQC x z.
Proof.
intros H1 H2 m.
transitivity (y m).
apply H1. apply H2.
Defined.

(* strange proofs ... *)
Lemma cIN_sound_right (A:class) (D k:Ens): A k -> EQC A D -> IN k D.
Proof.
intros H K. unfold EQC in K. apply K in H. simpl in H. exact H.
Defined.

Lemma cIN_sound_iff (A:class) (D k:Ens) (K:EQC A D): A k <-> IN k D.
Proof.
split;intros H;
 (*unfold EQC in K;*) apply K in H; (*simpl in H;*) exact H. (*twice*)
Defined.


(*
Существуют ли классы такие, что то, что они - множества
- недоказуемо? Да: определённые как ∅ или V, в зависимости от
недоказуемого и не опровержимого утверждения.
Можно ли, тем не менее, доказать, что образовывая синглтон из классов
я получу множество? Да, классически: элемент либо множество, либо нет.
Если нет, то получается ∅ .
xclass должен хранить либо подтверждение, либо опровержение своей
множественности.
Цель - получить систему, в которой можно игнорировать 
*)

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
(*      eapply EQC_tran.
      apply J.
      intros a. split; intro h.
simpl in h.
simpl.*)
Abort.

Theorem UPeI (X:Ens): EQ (Union (Power X)) X.
Proof.
apply axExt. intro z. split; intro H.
+ simpl in H. 
  apply Union_IN in H as [M [K1 K2]].
  apply IN_Power_INC in K1.
  apply K1.
  exact K2.
+ apply IN_Union with (E':=X).
  - apply INC_IN_Power. intros a K. exact K.
  - exact H.
Defined.

Theorem XiPUX (X:Ens): INC X (Power (Union X)).
Proof.
unfold INC.
intros A H.
apply INC_IN_Power.
intros B K.
apply IN_Union with (E':=A).
exact H.
exact K.
Defined.

Theorem nPUXiX : not (forall (X:Ens),INC (Power (Union X)) X).
Proof.
intro H.
pose (A:=H Vide).
pose (B:=A Vide).
assert (C:IN Vide (Power (Union Vide))).
+ apply INC_IN_Power.
  intros y J.
  apply Vide_est_vide in J as [].
+ apply B in C.
  apply Vide_est_vide in C as [].
Defined.

SearchPattern ( _ + _ = _ + _ ).

SearchPattern ( _ (Power _) ).

(*(*Variant isas2 (C : class) : Type :=
| Build_isas2 : forall (dmn : Ens) (_ : EQC C (stoc dmn)), isas2 C
| Build_isas3 : forall (dmn : Ens) (_ : EQC C (stoc dmn)), isas2 C. *)
Check isas2.
dmn isas
exact h.
      apply EQC_symm.

      apply axExtC.
     rewrite <- (eqvias A ASE) in J.
isas
(* apply axExtC in HA. *)
      apply IN_Paire_left.
      simpl.
      
ueapp scosisas.
simpl.
cPair
 eqn:M.
(*exact (Paire A B).
unfold isas.*)*)
(*Abort.*)

Record Category := {
Ob : class;
Hom : forall x y:Ens, Ob x -> Ob y -> Ens;
}.

(* to define *)
Definition OrdPair_fst : Ens->Ens.
Abort.

(********** LAST SECTION
Definition eFunc (x y:Ens) : Ens.
Proof.
ueapp Comp.
exact (Product x y).
intro f.
exact ((EQ (dom f) x) /\ True ).
Defined.

Definition Sets : Category.
Proof.
unshelve eapply Build_Category.
exact cV.
simpl.
intros x y _ _.
exact (eFunc x y).
Defined.

Theorem  domias (R:Ens) : (ias (cDom R)).
Proof.
unfold ias in *|-*.
exists (cPow (cUnion (cUnion R))).
intro w. split.
+ intro g.
  simpl in g.
  destruct g as [v wvir].
Power
Abort.

(* Functions *)

(*pose (i:=IN_Sing x).
enough (forall x z, (IN z (Sing x)) <-> (EQ z x)).*)

(* Other *)
Fixpoint nclass (n:nat) := 
match n with
| 0 => Ens
| S b => (nclass b)->Prop
end.
**********)