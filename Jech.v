(*
This library is a remake and extension of this library:
https://github.com/coq-contribs/zfc
I simplified proofs to get rid of unnecessary fixpoints and
to increase readability. (IMHO, it is much easier to read
Gallina's "match .. end" notation rather than discover 
induction and recursion principles.)
*)
(* IST = "Introduction to Set Theory".(K.Hrbacek, T.Jech)
    ST = "Set Theory".(T.Jech, 2003)
 I2AST = "Introduction to Axiomatic Set Theory"(W.Zaring,G.Takeuti)
   AST = "Axiomatic Set Theory"(W.Zaring,G.Takeuti)
*)
(*** Contents ***

Part I: Large isolated part of "/coq-contribs/zfc/" library and
proofs of some axioms of zfc (see "axChoice" theorem).

Part II: Development of the classic ZFC theory with
 exercises from Jech's "Set theory". (try to avoid classes)
and "Introduction t set theory" books.

Part III(empty): Development of formulas and derivations.
Here I'd like to implement well-known theorems about
1st-order logic.

Part IV: Experiments with classes and many theorem about them.

Part V: Translation of Metamath theorems.
( transfinite recursion )

APPENDIX:
* tiny experiments with ensembles
* Formulas for automatization of soundness proofs.
* trash section

*****************)

(* "presumption of unsoundness"
during the development of the part II
all definitions must be considered as unsafe before
 checking the proof of soundness.
See also part IV.
*)

(* AIMS:
 The first aim is to create a self-contained book 
of the first-order logic and ZFC set theory.
 The second aim is to solve exercises from Jech's "Set theory".
 The third aim is to re-use proofs from Metamath.
*)

(*Exercises from Jech: (search theses through the text)
  snis   :
  ex_1_2, ex_1_2', ex_1_3'' : ex.1.2
  ex_1_3 : ex.1.3
  ex_1_4 : ex.1.4
  ex_1_5 : ex.1.5
  ex_1_6 : ex.1.6
*)

(* TODO try to use constructible universe to avoid
 axSFC and LEM *)
(* (!) These notions (Pair, Union, Powerset) should not 
be unfolded during the proofs in Part II. *)
(* Is it possible not to use classes? *)

Require Import FunctionalExtensionality.
Require Import Logic.Classical_Prop.
Require Import Logic.Classical_Pred_Type.
Require Import Logic.ChoiceFacts.
Require Import Logic.IndefiniteDescription.

Axiom (axSFC:SetoidFunctionalChoice).
Definition ex2sig {A : Type} {P : A -> Prop}
 : (exists x : A, P x) -> {x : A | P x}
 := constructive_indefinite_description P.
(*
==============================================
                     Part I
==============================================
*)

(* The type representing sets
  (Ensemble = french for set) *)

Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.

(* Extensional equality of sets *)
Fixpoint EQ (E1 E2: Ens) {struct E2}: Prop :=
  match E1 with
   | sup A f =>
       match E2 with
       | sup B g =>
           (forall x : A, exists y : B, EQ (f x) (g y)) /\
           (forall y : B, exists x : A, EQ (f x) (g y))
       end
   end.

(* Membership on sets *)
Definition IN (E1 E2 : Ens) : Prop :=
  match E2 with
  | sup A f => exists y : A, EQ E1 (f y)
  end.

(* INCLUSION *)
Definition INC : Ens -> Ens -> Prop 
 := (fun E1 E2 : Ens => 
      forall E : Ens, IN E E1 -> IN E E2
    ).

(* EQ is an equivalence relation  *)
Fixpoint EQ_refl (E : Ens) : EQ E E.
Proof.
destruct E as [A f].
split; intros z; exists z; exact (EQ_refl (f z)).
Defined.

Fixpoint EQ_tran (E1 E2 E3 : Ens) {struct E2}:
 EQ E1 E2 -> EQ E2 E3 -> EQ E1 E3.
Proof.
destruct E1 as [A1 f1], E2 as [A2 f2], E3 as [A3 f3].
intros E1eqE2 E2eqE3.
destruct E1eqE2 as [E12 E21].
destruct E2eqE3 as [E23 E32].
simpl in |- *.
split.
+ intro x1.
  destruct (E12 x1) as [x2 P12].
  destruct (E23 x2) as [x3 P23].
  exists x3. apply (EQ_tran (f1 x1) (f2 x2) (f3 x3) P12 P23).
+ intro x3.
  destruct (E32 x3) as [x2 P32].
  destruct (E21 x2) as [x1 P21].
  exists x1. apply (EQ_tran (f1 x1) (f2 x2) (f3 x3) P21 P32).
Defined.

Fixpoint EQ_sym (E1 E2 : Ens) {struct E2}: EQ E1 E2 -> EQ E2 E1.
Proof.
intro H.
destruct E1 as [A f], E2 as [B g].
simpl in * |- *.
destruct H as [A2B B2A]; split.
+ intro b. destruct (B2A b) as [a J]. exists a. apply EQ_sym with (1:=J).
+ intro a. destruct (A2B a) as [b J]. exists b. apply EQ_sym with (1:=J).
Defined.

Hint Resolve EQ_sym EQ_refl : zfc.
(*Definition EQ_INC := INC_refl.*)

(* Membership is extentional (i.e. is stable w.r.t. EQ)   *)
Theorem IN_sound_left :
 forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
Proof.
intros A B C AeqB AinC.
destruct C as [T F].
simpl in * |- *.
destruct AinC as [Y AeqFY].
exists Y.
apply EQ_tran with A.
+ apply EQ_sym. exact AeqB.
+ apply AeqFY.
Defined.

Theorem IN_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
Proof.
intros A B C BeqC AinB.
destruct B as [Y G].
destruct C as [Z H].
simpl in *|-*.
destruct BeqC as [Y2Z Z2Y].
destruct AinB as [y AeqGy].
destruct (Y2Z y) as [z GyeqHz].
exists z.
eapply EQ_tran with (1:=AeqGy) (2:=GyeqHz).
Defined.

Theorem axExt_left : forall (x y : Ens),
  (forall z, IN z x <-> IN z y) -> EQ x y.
Proof.
intros x y K.
 induction x as [A f], y as [B g].
  simpl in * |- *.
  split.
  - intro x.
    apply K.
    exists x.
    apply EQ_refl.
  - intro y.
    assert (Q:exists y0 : B, EQ (g y) (g y0)).
    * exists y.
      apply EQ_refl.
    * destruct (proj2 (K (g y)) Q).
      exists x.
      apply EQ_sym.
      exact H0.
Defined.

Theorem axExt_right : forall x y : Ens,
   EQ x y -> forall z, (IN z x <-> IN z y).
Proof.
 intros.
  split.
  - apply IN_sound_right. exact H.
  - apply IN_sound_right. apply EQ_sym. exact H.
Defined.

Theorem axExt : forall x y : Ens,
   EQ x y <-> forall z, (IN z x <-> IN z y).
Proof.
intros.
split.
+ apply axExt_right.
+ apply axExt_left.
Defined.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
Proof.
intros E E' H z.
eapply axExt_right in H.
destruct H as [H1 H2].
exact H1.
Defined.

Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.

(* easy lemma *)
Theorem INC_antisym : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
Proof.
intros E E' H1 H2.
apply axExt_left.
intro z. split. apply H1. apply H2.
Defined.
Hint Resolve INC_antisym: zfc.

Theorem INC_EQ : forall E E' : Ens,
  INC E E' -> INC E' E -> EQ E E'.
Proof.
intros E E' H1 H2.
apply INC_antisym; assumption.
Defined.

(* Inclusion is reflexive, transitive, extentional *)
Theorem INC_refl : forall E : Ens, INC E E.
Proof.
unfold INC in |- *; auto with zfc.
Defined.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
Proof.
unfold INC in |- *; auto with zfc.
Defined.

Theorem INC_sound_left :
 forall A B C : Ens, EQ A B -> INC A C -> INC B C.
Proof.
intros A B C AeqB AincC Z ZinB.
apply AincC.
eapply IN_sound_right.
+ apply EQ_sym. exact AeqB.
+ exact ZinB.
Defined.

Theorem INC_sound_right :
 forall A B C : Ens, EQ B C -> INC A B -> INC A C.
Proof.
intros A B C BeqC AincB Z ZinA.
eapply IN_sound_right.
+ exact BeqC.
+ apply AincB.
  exact ZinA.
Defined.

(************ Remastered Axioms.v ***************)

(* Definitions of the empty set, pair, union, intersection, comprehension  *)
(*  axiom and powerset, together with their properties                     *)

(* The empty set  (vide = french for empty)   *)
Definition Vide : Ens :=
  sup False (fun x : False => match x return Ens with
                              end).

(* The axioms of the empty set *)
Definition Vide_est_vide : forall E : Ens, IN E Vide -> False.
Proof.
intro E.
intro H.
destruct H.
exact x.
Abort. (* nothing_IN_Vide = Vide_est_vide *)

Definition nothing_IN_Vide (E : Ens) (H:IN E Vide) : False
:= match H with
   | ex_intro _ x _ => x
   end.

(*tout_vide_est_Vide*)
Theorem empty_set_EQ_Vide :
 forall E : Ens, (forall E' : Ens, IN E' E -> False) -> EQ E Vide.
Proof.
intros E K.
destruct E as [A e].
simpl in *|-*.
split.
+ intro x.
  exfalso.
  apply (K (e x)).
  exists x.
  apply EQ_refl.
+ intro y. destruct y.
Defined.

(*Theorem tout_vide_est_Vide' :
 forall E : Ens, (forall E' : Ens, IN E' E -> False) -> EQ E Vide.
Proof.
 unfold Vide in |- *; simple induction E; simpl in |- *; intros A e H H0;
  split.
intros; elim (H0 (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.
Defined.*)

(* Pair *)

Definition Pair (A B:Ens) : Ens
 := sup bool (fun b : bool => if b then A else B).

(*Definition Pair : forall E E' : Ens, Ens.
Proof.
intros.
apply (sup bool).
simple induction 1.
exact E.
exact E'.
Show Proof.
Defined.*)

(* The pair construction is extensional *)
Theorem Pair_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Pair A B) (Pair A' B).
Proof.
unfold Pair in |- *.
simpl in |- *.
intros A A' B AeqA'; 
split; (intros [|]; 
 [exists true; exact AeqA' | exists false; exact (EQ_refl B)]
).
Defined.

Theorem Pair_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Pair A B) (Pair A B').
Proof.
unfold Pair in |- *; simpl in |- *; intros; split.
+ simple induction x.
  exists true; auto with zfc.
  exists false; auto with zfc.
+ simple induction y.
  exists true; auto with zfc.
  exists false; auto with zfc.
Defined.

Hint Resolve Pair_sound_right Pair_sound_left: zfc.

(* The axioms of the pair *)
Theorem IN_Pair_left : forall E E' : Ens, IN E (Pair E E').
Proof.
unfold Pair in |- *. simpl in |- *. exists true. simpl in |- *.
auto with zfc.
Defined.

Theorem IN_Pair_right : forall E E' : Ens, IN E' (Pair E E').
Proof.
unfold Pair in |- *. simpl in |- *. exists false. simpl in |- *.
exact (EQ_refl E').
Defined.

Theorem Pair_IN :
 forall E E' A : Ens, IN A (Pair E E') -> EQ A E \/ EQ A E'.
Proof.
unfold Pair in |- *; simpl in |- *.
intros E E' A [b P].
destruct b; auto with zfc.
Defined.

Hint Resolve IN_Pair_left IN_Pair_right nothing_IN_Vide: zfc.

(* The singleton set  *)
Definition Sing (E : Ens) := Pair E E.

(* The axioms  *)
Theorem IN_Sing : forall E : Ens, IN E (Sing E).
Proof.
unfold Sing in |- *; auto with zfc.
Defined.

Theorem IN_Sing_EQ : forall E E' : Ens, IN E (Sing E') -> EQ E E'.
Proof.
unfold Sing in |- *. 
intros E E' H.
apply Pair_IN in H as [H|H]; assumption.
Defined.

Hint Resolve IN_Sing IN_Sing_EQ: zfc.

Theorem Sing_sound : forall A A' : Ens, EQ A A' -> EQ (Sing A) (Sing A').
Proof.
unfold Sing in |- *; intros. apply EQ_tran with (Pair A A').
 auto with zfc.
 auto with zfc.
Defined.

Hint Resolve Sing_sound: zfc.

Theorem EQ_Sing_EQ : forall E1 E2 : Ens, EQ (Sing E1) (Sing E2) -> EQ E1 E2.
Proof.
intros. cut (IN E1 (Sing E2)).
+ intros. auto with zfc.
+ apply IN_sound_right with (Sing E1).
  - auto with zfc.
  - auto with zfc.
Defined.

Hint Resolve EQ_Sing_EQ: zfc.

(* We here need sigma types -- i.e. computational existentials *)
(*
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig A P.
*)

(* The set obtained by the comprehension (or separation) axiom *)

Definition Comp : Ens -> (Ens -> Prop) -> Ens.
Proof.
intros [A f] P.
apply (sup (sig (fun x:A => P (f x)))).
intros [x _].
exact (f x).
Defined.
(*simple induction 1; intros x p. todo: swap args*)

(* The comprehension/separation axioms *)
Theorem Comp_INC : forall (E : Ens) (P : Ens -> Prop), INC (Comp E P) E.
Proof.
intros E P z zinCompEP.
destruct E as [A f].
simpl in *|-*.
destruct zinCompEP as [w R].
destruct w as [a Pfa].
exists a. exact R.
Defined.

Theorem IN_Comp_P :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) -> IN A (Comp E P) -> P A.
Proof.
intros E A P H H0.
destruct E,H0,x as [a p].
apply H with (1:=p).
apply EQ_sym. assumption.
Defined.

(* I2AST p.13, thm 4.12, (<-) *)
Theorem IN_P_Comp :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) ->
 IN A E -> P A -> IN A (Comp E P).
Proof.
intros.
destruct E.
simpl in *|-*.
destruct H0 as [a p].
unshelve eapply ex_intro.
exists a.
apply H with (1:=H1).
exact p.
simpl.
exact p.
Defined.

(* Again, extentionality is not stated, but easy 
   only if P preserves EQ.
*)

(* Projections of a set: *)
(*  1: its base type     *)
Definition pi1 (X:Ens):Type
 := match X with
    | sup A _ => A
    end.

(*  2: the function      *)
Definition pi2 (X:Ens) (m:pi1 X):Ens 
:= match X as E return (pi1 E -> Ens) with
   | sup A f => fun k : pi1 (sup A f) => f k
   end m.

(* The Union set   *)
Definition Union : forall E : Ens, Ens.
Proof.
intros [A f].
apply (sup { x : A & pi1 (f x)} ).
intros [a b].
exact (pi2 (f a) b).
Defined.

Theorem EQ_EXType :
 forall E E' : Ens,
 EQ E E' ->
 forall a : pi1 E,
 exists b : pi1 E', EQ (pi2 E a) (pi2 E' b).
Proof.
intros [A f] [A' f'] [e1 e2].
simpl in |- *.
apply e1.
Defined.

Theorem IN_EXType :
 forall E E' : Ens,
 IN E' E -> exists a : pi1 E, EQ E' (pi2 E a).
Proof.
intros [A f]. simpl.
intros [A' f']. trivial.
Defined.

(* The union axioms *)
Theorem IN_Union :
 forall E E' E'' : Ens, IN E' E -> IN E'' E' -> IN E'' (Union E).
Proof.
intros E.
intros.
destruct E as [A f].
simpl in *|-*.
destruct H as [a E'eqfy].
unshelve eapply ex_intro.
+ exists a.
  destruct E' as [A' f'].
  simpl in *|-*.
  try destruct H0 as [a' E''eqf'y].
Abort.

Theorem IN_Union :
 forall E E' E'' : Ens, IN E' E -> IN E'' E' -> IN E'' (Union E).
Proof.
intros E E' E'' H H0.
destruct (IN_EXType E E' H) as [x e].
destruct E as [A f].
assert (e1 : EQ (pi2 (sup A f) x) E').
{ apply EQ_sym; exact e. }
assert (i1:IN E'' (pi2 (sup A f) x)).
{ apply IN_sound_right with E'; auto with zfc. }
apply IN_EXType in i1 as [x0 e2].
simpl in x0.
exists (existT (fun x : A => pi1 (f x)) x x0).
exact e2.
Defined.

Theorem IN_INC_Union : forall E E' : Ens, IN E' E -> INC E' (Union E).
Proof.
unfold INC in |- *.
intros [A f].
 simpl in |- *.
intros E' i E'' i'.
destruct (IN_EXType (sup A f) E' i) as [a e].
simpl in a, e.
destruct (IN_EXType E' E'' i') as [a' e''].
assert (i'': IN E'' (f a)).
{ apply IN_sound_right with E'; auto with zfc. (* e i' *) }
eapply IN_EXType in i'' as [aa ee].
exists (existT (fun x : A => pi1 (f x)) a aa).
exact ee.
Defined.

Theorem Union_IN :
 forall E E' : Ens,
 IN E' (Union E) -> exists E1 : Ens, IN E1 E /\ IN E' E1.
Proof.
intros [A f].
simpl in |- *.
simple induction 1.
intros [a b].
intros.
exists (f a).
split.
+ exists a; auto with zfc.
+ apply IN_sound_left with (pi2 (f a) b). 
  1 : auto with zfc.
  simpl in |- *.
  destruct (f a). simpl.
  exists b. auto with zfc.
Defined.

(* extentionality of union  *)
Theorem Union_sound : forall E E' : Ens, EQ E E' -> EQ (Union E) (Union E').
Proof.
unfold Union in |- *.
intros [A f] [A' f'].
 simpl in |- *.
 intros [e1 e2].
 split.
+ intros [a aa].
  destruct (e1 a) as [a' ea].
  destruct (EQ_EXType (f a) (f' a') ea aa) as [aa' eaa].
  exists (existT (fun x : A' => pi1 (f' x)) a' aa'); simpl in |- *;
  auto with zfc.
+ intros [a' aa'].
  destruct (e2 a') as [a ea].
  assert(ea': EQ (f' a') (f a)).
  { auto with zfc. }
  destruct (EQ_EXType (f' a') (f a) ea' aa') as [aa eaa].
  exists (existT (fun x : A => pi1 (f x)) a aa); auto with zfc.
Defined.


(* The union construction is monotone w.r.t. inclusion   *)
Theorem Union_mon : forall E E' : Ens, INC E E' -> INC (Union E) (Union E').
Proof.
unfold INC in |- *; intros E E' IEE E'' IEE''.
destruct (Union_IN E E'') as [E''' [I1 I2]].
+ auto with zfc.
+ apply IN_Union with E'''; auto with zfc.
Defined.

(*  The powerset and its axioms   *)
Definition Power (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun P : A -> Prop =>
         sup _
           (fun c : sigT (fun a : A => P a) =>
            match c with
            | @existT _ _ a p => f a
            end))
  end.

Theorem IN_Power_INC : forall E E' : Ens, IN E' (Power E) -> INC E' E.
Proof.
intros [A f].
intros E'.
intros [P H]. revert H.
destruct E' as [A' f'].
intros [HA HB].
intros E'' [a' e].
destruct (HA a') as [[a p] H].
intros; exists a.
apply EQ_tran with (f' a'); auto with zfc.
Defined.

Theorem INC_IN_Power : forall E E' : Ens, INC E' E -> IN E' (Power E).
Proof.
intros [A f].
intros [A' f'] i.
exists (fun a : A => IN (f a) (sup A' f')).
simpl in |- *.
split.
+ intros.
  elim (i (f' x)).
  - intros a e.
    cut (EQ (f a) (f' x)); auto with zfc.
    intros e1.
    exists
     (existT (fun a : A => exists y : A', EQ (f a) (f' y)) a
        (ex_intro (fun y : A' => EQ (f a) (f' y)) x e1)).
    simpl in |- *.
    auto with zfc.
  - auto with zfc.
    simpl in |- *.
    exists x; auto with zfc.
+ simple induction y; simpl in |- *.
  simple induction 1; intros.
  exists x0; auto with zfc.
Defined.

Theorem Power_mon : forall E E' : Ens, INC E E' -> INC (Power E) (Power E').
Proof.
intros.
unfold INC in |- *; intros.
apply INC_IN_Power.
cut (INC E0 E).
unfold INC in |- *; unfold INC in H; intros; auto with zfc.
apply IN_Power_INC; auto with zfc.
Defined.

Theorem Power_sound : forall E E' : Ens, EQ E E' -> EQ (Power E) (Power E').
Proof.
intros E E' e.
apply INC_antisym; unfold INC in |- *.
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
Theorem not_EQ_Sing_Vide : forall E : Ens, EQ (Sing E) Vide -> False.
Proof.
intros E e.
cut (IN E Vide).
+ simpl in |- *.
  intros [[]].
+ apply IN_sound_right with (Sing E); auto with zfc.
Defined.

Theorem not_EQ_Vide_Sing : forall E : Ens, EQ Vide (Sing E) -> False.
Proof.
intros E e.
cut (IN E Vide).
exact (nothing_IN_Vide E).
apply IN_sound_right with (Sing E).
+ auto with zfc.
+ auto with zfc.
Defined.

(*=== Omega.v ===*)

Definition Class_succ (E : Ens) := Union (Pair E (Sing E)).

Definition Nat : nat -> Ens.
Proof.
simple induction 1; intros.
exact Vide.
exact (Class_succ X).
Defined.

Definition Omega : Ens := sup nat Nat.

Theorem IN_Class_succ : forall E : Ens, IN E (Class_succ E).
Proof.
intros E; unfold Class_succ in |- *; unfold Sing in |- *;
 apply IN_Union with (Pair E E); auto with zfc.
Defined.

Theorem INC_Class_succ : forall E : Ens, INC E (Class_succ E).
Proof.
unfold INC in |- *; unfold Class_succ in |- *.
intros.
apply IN_Union with E; auto with zfc.
Defined.

Hint Resolve IN_Class_succ INC_Class_succ: zfc.

Theorem IN_Class_succ_or :
 forall E E' : Ens, IN E' (Class_succ E) -> EQ E E' \/ IN E' E.
Proof.
intros E E' i.
unfold Class_succ in i.
elim (Union_IN (Pair E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Pair_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
apply IN_sound_right with E1; auto with zfc.
Defined.

Theorem E_not_IN_E : forall E : Ens, IN E E -> False.
Proof.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.
simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
exists a; auto with zfc.
Defined.

Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
Proof.
intros; simpl in |- *; exists n; auto with zfc.
Defined.
Hint Resolve Nat_IN_Omega: zfc.

Theorem IN_Omega_EXType :
 forall E : Ens, IN E Omega -> exists n : nat, EQ (Nat n) E.
Proof.
simpl in |- *; simple induction 1.
intros n e.
exists n; auto with zfc.
Defined.

Theorem IN_Nat_EXType :
 forall (n : nat) (E : Ens),
 IN E (Nat n) -> exists p : nat, EQ E (Nat p).
Proof.
simple induction n.
+ simpl in |- *.
  simple induction 1.
  simple induction x.
+ intros.
  change (IN E (Class_succ (Nat n0))) in H0.
  elim (IN_Class_succ_or (Nat n0) E H0).
  - intros; exists n0.
    auto with zfc.
  - intros.
    elim (H E); auto with zfc.
Defined.

Theorem Omega_EQ_Union : EQ Omega (Union Omega).
Proof.
apply INC_antisym; unfold INC in |- *.
+ intros.
  elim (IN_Omega_EXType E H); intros n e.
  apply IN_Union with (Nat (S n)).
  - auto with zfc.
  - apply IN_sound_left with (Nat n).
    auto with zfc.
    change (IN (Nat n) (Class_succ (Nat n))) in |- *.
    auto with zfc.
+ intros.
  destruct (Union_IN Omega E H) as [e h].
  destruct h as [i1 i2].
  destruct (IN_Omega_EXType e i1) as [n e1].
  assert (H0: IN E (Nat n)).
  1 : apply IN_sound_right with e; auto with zfc.
  destruct (IN_Nat_EXType n E H0) as [x H1].
  apply IN_sound_left with (Nat x); auto with zfc.
Defined.

(*
Theorem Omega_Ord : (Ord Omega).

apply Eo with (Union Omega).
apply Lo.
intros.
elim (IN_Omega_EXType e H).
intros n ee.
apply Eo with (Nat n); Auto with zfc.
elim n.
auto with zfc.
auto with zfc.
intros.
change (Ord (Class_succ (Nat n0))); Auto with zfc.
apply EQ_sym; Auto with zfc.
apply Omega_EQ_Union.

Save.
*)

Fixpoint Vee (E : Ens) : Ens :=
  match E with
  | sup A f => Union (sup A (fun a : A => Power (Vee (f a))))
  end.

(*
Definition Alpha : (E:Ens)Ens.
(Induction E; Intros A f r).
apply Union.
apply (sup A).
intros a.
exact (Power (r a)).

Save.
Transparent Alpha.
*)

(*=== AXIOMS ===*)

(* page 3 *)
(* axExt see above *)
Theorem axPair : forall a b : Ens, exists w:Ens,
   forall z, (IN z w <-> EQ z a \/ EQ z b).
Proof.
intros a b.
exists (Pair a b).
intro z.
split.
+ apply Pair_IN.
+ intros [H|H].
  - eapply IN_sound_left.
    apply EQ_sym; exact H.
    apply IN_Pair_left.
  - eapply IN_sound_left.
    apply EQ_sym in H; exact H.
    apply IN_Pair_right.
Defined.

Theorem axUnion : forall X : Ens, exists Y:Ens,
   forall z, (IN z Y <-> exists m:Ens, IN m X /\ IN z m).
Proof.
intros X.
exists (Union X).
intro z; split; intro H.
+ apply Union_IN.
  assumption.
+ destruct H as [m [minX zinm]].
  eapply IN_Union.
  exact minX.
  exact zinm.
Defined.

Theorem axPower : forall X : Ens, exists Y:Ens,
   forall z, (IN z Y <-> INC z X).
Proof.
intros.
exists (Power X).
intro z; split; intro H.
+ apply IN_Power_INC.
  exact H.
+ apply INC_IN_Power.
  exact H.
Defined.

(*=== 3_Regularity.v ===*)

(* Epsilon induction. *)
Theorem eps_ind (R:Ens->Prop)
(Sou_R:forall a b, EQ a b -> (R a <-> R b))
: (forall x:Ens, (forall y, IN y x -> R y) -> R x)
-> forall z, R z.
Proof.
intros.
induction z.
apply H.
simpl.
intros y q.
destruct q as [a G].
rewrite  (Sou_R y (e a)).
apply H0.
exact G.
Defined.

(* (regular_over x) means
"Every set that contains x as an element is regular." *)
Definition regular_over x := forall u : Ens, (IN x u -> exists y,
IN y u /\ forall z, IN z u -> ~ IN z y).

Definition epsmin a b := IN a b /\ forall c, IN c b -> ~ IN c a.

(* Soundness of the definition of regular_over. *)
Theorem regular_over_sound : forall a b : Ens, 
 EQ a b -> regular_over a <-> regular_over b.
Proof.
intros.
unfold regular_over.
split; intros.
+ apply IN_sound_left with (E':=a) in H1.
  apply H0. apply H1.
  apply EQ_sym. exact H.
+ apply IN_sound_left with (E':=b) in H1.
  apply H0. apply H1.
  exact H.
Defined.

(* Here I follow Zuhair's proof from source.
https://math.stackexchange.com/users/489784/zuhair *)

(* Unending chain *)
Definition UC c := forall m, IN m c -> exists n, IN n m /\ IN n c.
Definition WF x := ~(exists c, UC c /\ IN x c).

(* Inductive step *)
Theorem Zuhair_1 (a:Ens): (forall x, IN x a -> WF x) -> WF a.
Proof.
unfold WF.
intros H K0.
pose (K:=K0).
destruct K as [c [M1 M2]].
unfold UC in M1.
pose (B:=M1 a M2).
destruct B as [n [nina ninc]].
apply (H n nina).
exists c.
split.
exact M1.
exact ninc.
Defined.

(* Soundness of WF *)
Theorem sou_WF : forall a b : Ens, EQ a b -> WF a <-> WF b.
Proof.
intros.
unfold WF.
* split.
+ intros A B.
  apply A.
  destruct B as [c [a1 a2]].
  exists c.
  split. exact a1.
  apply IN_sound_left with (E:=b).
  apply EQ_sym. exact H.
  exact a2.
+ intros A B.
  apply A.
  destruct B as [c [a1 a2]].
  exists c.
  split. exact a1.
  apply IN_sound_left with (E:=a).
  exact H.
  exact a2.
Defined.

(* Induction. "Every set is well-founded." *)
Theorem Zuhair_2 (y:Ens): WF y.
Proof.
apply eps_ind.
- exact sou_WF.
- intros a. exact (Zuhair_1 a).
Defined.

(* Formalization of Andreas Blass variant of proof. 
https://math.stackexchange.com/users/48510/andreas-blass *)

Theorem Blass x : regular_over x.
Proof.
unfold regular_over.
pose (A:=Zuhair_2 x); unfold WF in A.
intros u xinu.
(* Series of the equivalent tranformations.*)
apply not_ex_all_not with (n:=u) in A.
apply not_and_or in A.
 destruct A as [H1|H2].
 2 : destruct (H2 xinu).
 unfold UC in H1.
apply not_all_ex_not in H1.
 destruct H1 as [yy yH].
 exists yy.
apply imply_to_and in yH.
 destruct yH as [Ha Hb].
 split. exact Ha.
 intro z.
apply not_ex_all_not with (n:=z) in Hb.
apply not_and_or in Hb.
 intro v.
 destruct Hb as [L0|L1]. exact L0.
 destruct (L1 v).
Defined.

(* Standard formulation of the regularity axiom. *)
Theorem axReg (x:Ens) :
(exists a, IN a x)->(exists y, IN y x /\ ~ exists z, IN z y /\ IN z x)
.
Proof.
pose (Q:= Blass).
unfold regular_over in Q.
intro e.
destruct e as [z zinx].
pose (f:= Q z x zinx).
destruct f as [g G].
exists g.
destruct G as [G1 G2].
split.
+ exact G1.
+ intro s.
  destruct s as [w [W1 W2]].
  exact (G2 w W2 W1).
Defined.

(* Other theorems *)

(* every set is a class *)
(* 1) function *)
Theorem esiacf : Ens -> (Ens -> Prop).
Proof.
intro e.
exact (fun x => IN x e).
Defined.

(* "is a set" predicate *)
Definition ias1 (s: Ens -> Prop) : Prop.
Proof.
exact (exists x:Ens, forall w, s w <-> esiacf x w).
Defined.

(* class must respect extensional equality
   sree is a witness of the soundness of class' definition *)
Section TheoremsAboutClasses.
Context (s:Ens->Prop)
        (sree : forall (w1 w2:Ens), EQ w1 w2 -> s w1 <-> s w2).

Theorem rewr (w1 w2:Ens) (J:s w1) (H : EQ w1 w2) : s w2.
Proof.
rewrite <- (sree w1 w2); assumption.
Defined.

(* subclass of a set is a set *)
Theorem scosias1 (m:Ens) 
(sc : forall x, s x -> (esiacf m) x) 
: ias1 s.
Proof.
unfold ias1.
unfold esiacf in * |- *.
(* { x e. m | s x }*)
exists (Comp m s).
intro w.
split.
+ intro u.
  pose(y:=sc w u).
  unfold esiacf in * |- *.
  apply IN_P_Comp.
  * intros w1 w2 K H.
    apply (rewr _ _  K H).
  * exact y.
  * exact u.
+ intro u.
  apply (IN_Comp_P m).
  exact rewr.
  exact u.
Defined.

End TheoremsAboutClasses.

(*Require Import ZFC.Ordinal_theory.*)
Theorem Class_succ_sound X Y (H: EQ X Y) :
EQ (Class_succ X) (Class_succ Y).
Proof.
unfold Class_succ.
assert (L1: EQ (Pair X (Sing X)) (Pair Y (Sing Y))).
2 : apply Union_sound in L1; exact L1.
apply EQ_tran with (E2:=Pair Y (Sing X)).
+ apply Pair_sound_left; exact H.
+ apply Pair_sound_right. apply Sing_sound. exact H.
Defined.

Theorem axInf : exists X, (IN Vide X /\ 
forall Y, (IN Y X -> IN (Class_succ Y) X)
).
Proof.
exists Omega.
split.
+ unfold Omega.
  unfold IN.
  exists 0.
  apply EQ_refl.
+ intros Y YinOm.
  apply IN_Omega_EXType in YinOm.
  destruct YinOm as [x H].
  assert (as1: EQ (Class_succ (Nat x)) (Class_succ Y)).
  apply Class_succ_sound. exact H.
  apply (IN_sound_left _ _ _ as1).
  (*Eval simpl in (Nat (S x)).*)
  apply (Nat_IN_Omega (S x)).
Defined.

Definition sOmega : Ens := proj1_sig (ex2sig axInf).

(*============================================
                     Part II
==============================================*)

(* Traditional Product needs Kuratowski ordered pair *)

(* Kuratowski construction *)
Definition OrdPair (x y : Ens) := Pair (Sing x) (Pair x y).

Theorem OrdPair_sound_left (x1 x2 y : Ens) (H : EQ x1 x2)
 : EQ (OrdPair x1 y) (OrdPair x2 y).
Proof.
unfold OrdPair.
apply EQ_tran with (E2:=Pair (Sing x1) (Pair x2 y)).
+ eapply Pair_sound_right.
  eapply Pair_sound_left.
  assumption.
+ eapply Pair_sound_left.
  eapply Sing_sound.
  assumption.
Defined.

Theorem OrdPair_sound_right (x y1 y2 : Ens) (H : EQ y1 y2)
 : EQ (OrdPair x y1) (OrdPair x y2).
Proof.
unfold OrdPair.
eapply Pair_sound_right.
eapply Pair_sound_right.
assumption.
Defined.

Lemma SingEqPair x y1 y2 (J: EQ (Sing x) (Pair y1 y2)) :
EQ x y1 /\ EQ x y2.
Proof.
apply EQ_sym in J.
pose (i1:=IN_Pair_left y1 y2).
apply IN_sound_right with (1:=J) in i1.
apply IN_Sing_EQ, EQ_sym in i1.
pose (i2:=IN_Pair_right y1 y2).
apply IN_sound_right with (1:=J) in i2.
apply IN_Sing_EQ, EQ_sym in i2.
split; assumption.
Defined.

Lemma Pair_sound (a b c d:Ens) (L:EQ a c) (R:EQ b d) 
 : EQ (Pair a b) (Pair c d).
Proof.
  apply EQ_tran with (E2:= Pair a d).
  apply Pair_sound_right, R.
  apply Pair_sound_left, L.
Defined.

Lemma Pair_EQ_cases a b c d (H:EQ (Pair a b) (Pair c d)) : 
(EQ a c \/ EQ a d)/\(EQ b c \/ EQ b d).
Proof.
rewrite axExt in H.
split.
+ destruct (H a) as [W1 _].
  assert (E := W1 (IN_Pair_left a b)).
  apply Pair_IN. assumption.
+ destruct (H b) as [W1 _].
  assert (E := W1 (IN_Pair_right a b)).
  apply Pair_IN. assumption.
Defined.

Theorem OrdPair_inj : forall a b c d : Ens, 
  EQ (OrdPair a b) (OrdPair c d)->(EQ a c/\EQ b d).
Proof. 
unfold OrdPair in |- *. intros.
pose (H1:=H).
apply Pair_EQ_cases in H1 as [K1 K2].
split.
+ destruct K1 as [A|B].
   apply EQ_Sing_EQ. assumption.
   apply SingEqPair in B as [n1 n2]. assumption.
+ destruct K1 as [A|B], K2 as [C|D].
 (*as [[A|B] [C|D]].*)
- (*split. apply EQ_Sing_EQ. assumption.*)
  apply EQ_sym in C.
  apply SingEqPair in C as [J1 J2].
  assert(i: EQ (Pair (Sing a) (Pair a b))
                (Sing (Sing a) )).
   apply Pair_sound_right.
   apply Pair_sound_right.
   apply EQ_sym in J2.
   eapply EQ_tran with (E2:=c); assumption.
  apply EQ_sym, EQ_tran with (2:=H) in i.
  apply SingEqPair in i as [F1 F2].
  apply SingEqPair in F2 as [U1 U2].
  eapply EQ_tran. apply EQ_sym. exact J2.
  eapply EQ_tran. apply EQ_sym. exact U1.
  exact U2.
- pose (i:=IN_Pair_right c d).
  eapply IN_sound_right in i.
  2 : { apply EQ_sym, D. }
  apply Pair_IN in i as [X1|X2].
  2 : { apply EQ_sym, X2. }
  pose (y:=IN_Pair_right a b).
  eapply IN_sound_right in y.
  2 : { apply D. }
  apply Pair_IN in y as [Y1|Y2].
   apply EQ_Sing_EQ in A.
   apply EQ_tran with (E2:=c). assumption.
   apply EQ_sym, EQ_tran with (E2:=a); assumption.
  assumption.
- apply EQ_sym, SingEqPair in C as [F1 F2].
  apply SingEqPair in B as [P1 P2].
  apply EQ_tran with (E2:=c). apply EQ_sym; exact F2.
  apply EQ_tran with (E2:=a). apply EQ_sym; exact P1.
  exact P2.
- pose (i:=IN_Pair_right c d).
  eapply IN_sound_right in i.
  2 : { apply EQ_sym, D. }
  apply Pair_IN in i as [X1|X2].
  2 : { apply EQ_sym, X2. }
  assert (v:EQ (Sing a) (Pair a b)).
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

(* technical theorem for rewrite tactic *)
Theorem two_sided (C : Ens -> Prop) :
(forall a b : Ens, EQ a b -> C a -> C b)
->
(forall a b : Ens, EQ a b -> C a <-> C b).
Proof.
intros.
split;intros H1.
- eapply (H a b). exact H0. exact H1.
- apply EQ_sym in H0.
  eapply (H b a). exact H0. exact H1.
Defined.

Theorem two_sided2 (C:Ens->Ens):
(forall X Y : Ens,
EQ X Y -> forall z : Ens, IN z (C X) -> IN z (C Y))
->
(forall X Y : Ens,
EQ X Y -> forall z : Ens, IN z (C X) <-> IN z (C Y)).
Proof.
intros H X Y XeqY z.
split.
+ apply H; assumption.
+ apply H; auto with zfc.
Defined.

Theorem Comp_sound_left (P:Ens->Prop)
(P_sound:forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2)
 (X Y:Ens) (H:EQ X Y) : EQ (Comp X P) (Comp Y P).
Proof.
apply axExt.
revert X Y H; apply two_sided2; intros X Y H.
intro z.
intro K.
  apply IN_P_Comp.
  exact P_sound.
  - apply IN_sound_right with (1:=H).
    eapply Comp_INC.
    exact K.
  - eapply IN_Comp_P in K.
    * exact K.
    * exact P_sound.
Defined.

Theorem cEQ_pres_soundness (P R:Ens->Prop)
(H:forall w1 w2 : Ens, EQ w1 w2 -> P w1 <-> R w2)
(P_sound:forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2)
:forall w1 w2 : Ens, R w1 -> EQ w1 w2 -> R w2.
Proof.
intros.
apply (proj1 (H w1 w2 H1)).
apply EQ_sym in H1.
apply (P_sound w2 w1).
apply (proj2 (H w2 w1 H1)).
exact H0.
exact H1.
Defined.

Definition SoundPred (P:Ens->Prop)
:= (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2).
 
Definition SoundCongl (A:(Ens->Prop)->Prop) :=
forall P R:Ens->Prop, SoundPred P  ->
(forall w : Ens, P w <-> R w)-> (A P -> A R).
(* maybe add P_sound *)

Theorem cEQ_works (P R:Ens->Prop)
(A:(Ens->Prop)->Prop)
(A_sound: True)
(H:forall w : Ens, P w <-> R w)
(P_sound:forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2)
: (A P) <-> (A R).
Proof.
split; intro J.
Abort.

Theorem pred_sou (P R:Ens->Prop)
(H:forall w : Ens, P w <-> R w)
(P_sound:forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2)
: forall w1 w2 : Ens, R w1 -> EQ w1 w2 -> R w2.
Proof.
intros.
apply (proj1 (H w2)).
apply (P_sound w1 w2).
2 : exact H1.
apply (proj2 (H w1)).
exact H0.
Defined.

Section cngl_sec.
Context (X z : Ens).

Check SoundCongl (fun P=>IN z (Comp X P)).
Theorem cngl_thm : SoundCongl (fun P=>IN z (Comp X P)).
Proof.
unfold SoundCongl.
intros.
Abort.
End cngl_sec.

Theorem Comp_sound_right (P R:Ens->Prop)
(P_sound:forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2)
(H:forall w : Ens, P w <-> R w)
 (X:Ens) : EQ (Comp X P) (Comp X R).
Proof.
apply axExt.
intro z.
(*revert P R H. simpl.*)
 split; intro q. (*TODO: REDUCE PROOF BY REMOVING SPLIT *)
+ apply IN_P_Comp.
  - apply (pred_sou P R H P_sound).
  - apply (Comp_INC X P z q).
  - apply (proj1 (H z)).
    apply (IN_Comp_P X); assumption.
+ apply IN_P_Comp.
  - apply P_sound.
  - apply (Comp_INC X R z q).
  - apply (proj2 (H z)).
    apply (IN_Comp_P X).
    * apply (pred_sou P R H P_sound).
    * assumption.
Defined.

Theorem Comp_sound (P R:Ens->Prop)
(P_sound:forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2)
(PeqvR:forall w : Ens, P w <-> R w)
 (X Y:Ens) (H:EQ X Y) : EQ (Comp X P) (Comp Y R).
Proof.
eapply EQ_tran with (E2:= (Comp Y P)).
+ apply Comp_sound_left; assumption.
+ apply Comp_sound_right; assumption.
Defined.

(* The Intersection of a nonempty set.  *)
Definition Inter (E : Ens) : Ens :=
  Comp (Union E) (fun e : Ens => forall a : Ens, IN a E -> IN e a).

Theorem Inter_sound (X Y:Ens) (H:EQ X Y): EQ (Inter X) (Inter Y).
Proof.
unfold Inter.
apply Comp_sound.
+ intros.
  eapply IN_sound_left.
  exact H1.
  exact (H0 a H2).
+ intro w. split.
  - intros. apply H0.
    eapply IN_sound_right.
    apply EQ_sym, H.
    assumption.
  - intros. apply H0.
    eapply IN_sound_right.
    apply H.
    assumption.
+ apply Union_sound; assumption.
Defined.

Theorem IN_Inter_all :
 forall E E' : Ens,
 IN E' (Inter E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
Proof.
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
Proof.
unfold Inter in |- *.
intros.
apply IN_P_Comp.
intros; apply IN_sound_left with w1; auto with zfc.
+ apply IN_Union with (E' := E''); auto with zfc.
+ auto.
Defined.

(* predicate for separation of the product *)
Definition inProduct (X Y u:Ens) :=
 exists (x y:Ens), (EQ u (OrdPair x y)) /\ IN x X /\ IN y Y.

(* Product of sets *)
Definition Product (X Y:Ens) :=
Comp
 (Power (Power (Union (OrdPair X Y))))
 (inProduct X Y)
.

Definition inDom (R u:Ens) := 
 exists (v:Ens), IN (OrdPair u v) R.

Definition dom (R:Ens) :=
Comp
 (Union (Union R))
 (inDom R)
.

Definition inRan (R u:Ens) := 
 exists (v:Ens), IN (OrdPair u v) R.

Definition ran (R:Ens) :=
Comp
 (Union (Union R))
 (inRan R)
.

Definition field (R:Ens) : Ens := Union (Pair (dom R) (ran R)).

Definition isFunction (X Y f:Ens) : Prop := (EQ (dom f) X)/\(INC (ran f) Y).

Definition functions (X Y:Ens) : Ens :=
Comp
 (Power (Product X Y))
 (isFunction X Y)
.

Definition fun1to1 (X Y:Ens) : Ens :=
Comp
 (functions X Y)
 (fun f => forall x1 x2 y, IN (OrdPair x1 y) f /\ IN (OrdPair x2 y) f 
 -> EQ x1 x2)
.

Definition restriction (X0 Y0 f X:Ens) (H:IN f (functions X0 Y0)) : Ens 
:=
Comp
 f
 (fun e => exists x y, EQ e (OrdPair x y) /\ IN x X)
.

(* Here we use epsilon-induction. *)
Theorem snis Y : ~(IN Y Y).
Proof.
apply (eps_ind (fun Y => ~(IN Y Y))).
+ intros a b aeqb.
  split;intros H K.
  - eapply IN_sound_right with (E'':=a) in K.
    eapply IN_sound_left with (E':=a) in K.
    exact (H K).
    apply EQ_sym; assumption.
    apply EQ_sym; assumption.
  - eapply IN_sound_right with (E'':=b) in K.
    eapply IN_sound_left with (E':=b) in K.
    exact (H K).
    assumption.
    assumption.
+ intros x H xinx.
  pose (Q:=H x xinx).
  exact (Q xinx).
Defined.

(* ex.1.2 p.22 *)
Theorem ex_1_2 : ~( exists X:Ens, INC (Power X) X).
Proof.
intros [X H].
apply INC_IN_Power in H.
apply snis in H.
exact H.
Defined.

(* it's for Comp ax *)
Lemma ex_1_2_lem : forall w1 w2 : Ens, ~ IN w1 w1 -> EQ w1 w2 -> ~ IN w2 w2.
Proof.
intros w1 w2 H1 H2 Y.
  apply H1.
  apply EQ_sym in H2.
  apply IN_sound_left with (E':=w1) in Y.
  apply IN_sound_right with (E'':=w1) in Y.
  exact Y. assumption. assumption.
Defined.

(* Here we will not use epsilon-induction. *)
Theorem ex_1_2' : ~( exists X:Ens, INC (Power X) X).
Proof.
intros [X H].
pose (S:= Comp X (fun x => ~ IN x x)).
assert (Q : INC S X).
apply Comp_INC.
apply INC_IN_Power in Q.
apply H in Q.
destruct (classic (IN S S)).
2 : { 
assert (R:IN S S).
apply IN_P_Comp.
- apply ex_1_2_lem.
- exact Q.
- exact H0.
- exact (H0 R).
}
pose (H1:=H0).
apply IN_Comp_P in H1.
exact (H1 H0).
apply ex_1_2_lem.
Defined.

(* Here we will not use both epsilon-induction
 and the law of the excluded middle. *)
Theorem ex_1_2'' : ~( exists X:Ens, INC (Power X) X).
Proof.
intros [X H].
pose (S:= Comp X (fun x => ~ IN x x)).
assert (Q : INC S X).
apply Comp_INC.
apply INC_IN_Power in Q.
apply H in Q.
assert (R1:~(IN S S)).
 intro H0.
 pose (H1:=H0).
 apply IN_Comp_P in H1.
 exact (H1 H0).
 apply ex_1_2_lem.
{ assert (R:IN S S).
 + apply IN_P_Comp.
  - apply ex_1_2_lem.
  - exact Q.
  - exact R1.
 + exact (R1 R). }
Defined.

(* Subset of X which consist of subsets of X. *)
Definition SoS (X:Ens) : Ens := Comp X (fun x => INC x X).

Definition Ind (X:Ens) : Prop := 
(IN Vide X) /\ (forall Y:Ens, IN Y X -> IN (Class_succ Y) X).

Lemma INC_Vide (X:Ens): INC Vide X.
Proof.
unfold INC. intros E IN_E_Vide.
destruct (nothing_IN_Vide E IN_E_Vide).
Defined.

(* it's for Comp ax *)
Lemma ex_1_3_lem : 
forall Y w1 w2 : Ens,
IN (Class_succ Y) w1 -> EQ w1 w2 -> IN (Class_succ Y) w2.
Proof.
intros Y w1 w2 H1 H2.
eapply IN_sound_right with (E':=w1).
exact H2.
exact H1.
Defined.

(* SoS is inductive *)
Theorem ex_1_3 (X:Ens) (H: Ind X) : Ind (SoS X).
Proof.
unfold SoS, Ind in * |- *.
constructor. (*split.*)
+ apply IN_P_Comp.
  - intros w1 w2 INC_w1_X EQ_w1_w2.
    eapply INC_sound_left. exact EQ_w1_w2. exact INC_w1_X.
  - firstorder.
  - exact (INC_Vide X).
+ intros x H0.
  pose (H1:=H0).
  unshelve eapply IN_Comp_P with (E:=X) in H1.
2 : { intros. apply INC_sound_left with (1:=H3). exact H2. }
(*(E:=w1). exact H3. exact H2. }*)
  apply Comp_INC in H0.
  destruct H as [Ha Hb].
  assert (xusxinX : IN (Class_succ x) X).
   apply Hb. exact H0.
  apply IN_P_Comp.
  { intros. unshelve eapply INC_sound_left (*with (E:=w1)*).
exact w1. exact H2. exact H. }
  exact xusxinX.
  intros M J.
  apply IN_Class_succ_or in J as [L1|L2].
  - apply IN_sound_left with (E:=x); assumption.
  - apply H1. assumption.
Defined.

Lemma ex_1_4_lem : forall w1 w2 : Ens,
(forall z : Ens, IN z w1 -> INC z w1) ->
EQ w1 w2 -> forall z : Ens, IN z w2 -> INC z w2.
Proof.
  { intros.
    eapply INC_sound_right. exact H0.
    apply H.
    eapply IN_sound_right. apply EQ_sym. exact H0. exact H1.
  }
Defined.

Definition isTrans := (fun x:Ens => forall z, IN z x -> INC z x).

Theorem sutra E (H:isTrans E): isTrans (Class_succ E).
Proof.
intros w K.
apply IN_Class_succ_or in K as [L|R].
+ eapply INC_sound_left.
  exact L.
  eapply INC_Class_succ.
+ apply H in R.
  intros q qinw. 
  eapply INC_Class_succ.
  apply R.
  exact qinw.
Defined.

Theorem ex_1_4 (X:Ens) (H: Ind X) 
 : Ind (Comp X isTrans).
Proof.
destruct H as [Ha Hb].
split.
+ apply IN_P_Comp.
  { exact ex_1_4_lem. }
  { exact Ha. }
  { intros x H. destruct (nothing_IN_Vide _ H). }
+ intros Y H.
  apply IN_Comp_P in H as H1.
  2 : exact ex_1_4_lem.
  apply Comp_INC in H as H0.
  clear H.
  apply Hb in H0.
  apply sutra in H1.
  apply IN_P_Comp.
  exact ex_1_4_lem.
  exact H0. exact H1.
Defined.

Theorem isTrans_sound (w1 w2:Ens) (eqw1w2 : EQ w1 w2) (H1 : isTrans w1)
 : isTrans w2.
Proof.
unfold isTrans in * |- *.
intros z zinw2.
eapply INC_sound_right.
exact eqw1w2.
apply H1.
eapply IN_sound_right.
apply EQ_sym.
exact eqw1w2.
exact zinw2.
Defined.

Lemma ex_1_5_lem1 : forall w1 w2 : Ens,
isTrans w1 /\ ~ IN w1 w1 -> EQ w1 w2 -> isTrans w2 /\ ~ IN w2 w2.
Proof.
intros w1 w2 [H1 H2] eqw1w2.
split.
+ eapply isTrans_sound.
  exact eqw1w2.
  exact H1.
+ intro w2inw2.
  apply H2.
  apply EQ_sym in eqw1w2 as eqw2w1.
  eapply IN_sound_right.
  exact eqw2w1.
  eapply IN_sound_left.
  exact eqw2w1.
  exact w2inw2.
Defined.

Theorem isTrans_Vide : isTrans Vide.
Proof.
unfold isTrans.
intros z zinvide.
destruct (nothing_IN_Vide z zinvide).
Defined.

Theorem ex_1_5 (X:Ens) (H: Ind X) 
 : Ind (Comp X (fun x => (isTrans x)/\~(IN x x))).
Proof.
destruct H as [Ha Hb].
split.
+ apply IN_P_Comp.
  exact ex_1_5_lem1.
  exact Ha.
  split.
  * exact isTrans_Vide.
  * intro videinvide. destruct (nothing_IN_Vide Vide videinvide).
+ intros Y H.
  apply IN_Comp_P in H as H1.
  2 : exact ex_1_5_lem1.
  apply Comp_INC in H as H0.
  clear H.
  apply Hb in H0.
   destruct H1 as [H1 H1'].
  apply sutra in H1 as isTrans_succ_Y.
  apply IN_P_Comp.
  exact ex_1_5_lem1. (*exact lem_ex_1_4.*)
  exact H0.
   split.
  exact isTrans_succ_Y.
   intro G.
  apply IN_Class_succ_or in G as [G1|G2].
  - pose (Q:=IN_Class_succ Y).
    eapply IN_sound_right in Q.
    2 : { apply EQ_sym. exact G1. }
    exact (H1' Q).
  - apply H1 in G2.
    pose (J:= IN_Class_succ Y).
    apply G2 in J.
    exact (H1' J).
Defined.

(* useless lemma: *)
Lemma lem2_l1 E Y (B:~EQ E Y): IN E (Class_succ Y) -> IN E Y.
Proof.
intro r.
apply IN_Class_succ_or in r as [G1|G2].
2 :  exact G2.
apply EQ_sym in G1.
destruct (B G1).
Defined.

(* unfinished: NN - natural numbers.
Theorem : forall x:Ens, IN x NN -> ~ IN x x.
Abort.

Theorem : forall x:Ens, IN x NN -> ~ EQ x (Class_succ x).
Abort.
*)

Definition Inhab z := exists x, IN x z.

Definition Epsmin t z := forall s, IN s z -> ~IN s t.

Lemma ex_1_6_lem1 : forall w1 w2 : Ens,
isTrans w1 /\
(forall z : Ens,
 Inhab z /\ INC z w1 -> exists t : Ens, IN t z /\ Epsmin t z) ->
EQ w1 w2 ->
isTrans w2 /\
(forall z : Ens,
 Inhab z /\ INC z w2 -> exists t : Ens, IN t z /\ Epsmin t z)
.
Proof.
intros w1 w2 [H1 H2] eqw1w2.
split.
+ eapply isTrans_sound.
  exact eqw1w2.
  exact H1.
+ intros z [inhz inczw2].
  eapply INC_sound_right in inczw2 as inczw1.
  2 : { apply EQ_sym. exact eqw1w2. }
  pose (Q:=H2 z (conj inhz inczw1)).
  destruct Q as [t [J1 J2]].
  exists t.
  firstorder.
Defined.

Theorem ex_1_6 (X:Ens) (H: Ind X) 
 : Ind (Comp X (fun x => (isTrans x)/\(
forall z, Inhab z /\ INC z x -> exists t, IN t z /\ (Epsmin t z) ))).
Proof.
pose (H1:=H).
destruct H1 as [H1 H2].
split.
+ apply IN_P_Comp.
  exact ex_1_6_lem1.
  assumption.
  split.
(* Тут можно двумя способами, либо повторить код: *)
(*  apply isTrans_Vide. *)
(* Либо вытащить : *)
  { pose (W := ex_1_5 X H).
    destruct W as [P1 P2].
    apply IN_Comp_P in P1 as [P1' P1''].
    exact P1'.
    exact ex_1_5_lem1. }
Abort.

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
Record class := Build_class' {
 prty :> Ens->Prop;
 sound : forall (a b : Ens), EQ a b -> (prty a -> prty b);
}.

Definition Build_class : forall Vprty : Ens -> Prop,
       (forall a b : Ens, EQ a b -> Vprty a <-> Vprty b) -> class.
Proof.
intros.
unshelve eapply Build_class'.
+ exact Vprty.
+ intros a b aeqb.
  apply (H a b aeqb).
Defined.

(* little transformation of a soundness predicate *)
Theorem sound_transf (T:class) (s:
forall (a b : Ens), EQ a b -> T a <-> T b ) :
forall w1 w2 : Ens, T w1 -> EQ w1 w2 -> T w2 .
Proof.
intros w1 w2 Tw1 w1eqw2.
apply (proj1 (s w1 w2 w1eqw2) Tw1).
Defined.



Definition cEQ (A B:class) := forall z:Ens, (prty A) z <-> (prty B) z.
(*
Definition cEQ (A B: Ens->Prop) := forall z:Ens, A z <-> B z.
*)
(* "is a set" predicate on classes *)
Definition ias (s: class) : Prop.
Proof.
exact (exists (x:Ens), forall w, s w <-> IN w x).
Defined.

(* "is a set" is a sound property on classes. *)
Definition ias_sound (A B: class)
(w:cEQ A B) (H:ias A): ias B.
Proof.
unfold ias in * |- *.
destruct H as [x eqv].
exists x.
intro z.
unfold cEQ in w.
rewrite <- w.
apply eqv.
Defined.

(*Lemma sousym (K:Ens->Prop)
(H:forall (a b : Ens), EQ a b -> (K a -> K b))
: forall (a b : Ens), EQ a b -> (K a <-> K b).
Proof.
intros a b aeqb. split.
apply (H a b aeqb).
apply H. apply EQ_sym. exact aeqb.
Defined.
Check two_sided.
*)


(* Class of all sets *)
Definition cV : class.
Proof.
unshelve eapply Build_class'.
+ intro z. exact True.
+ simpl. intros a b H1 H2. exact H2.
Defined.

(* Empty class *)
Definition cE : class.
Proof.
unshelve eapply Build_class'.
+ intro z. exact False.
+ simpl. intros a b H1 H2. exact H2.
Defined.

(* I2AST p.13, thm 4.12, (->) *)
Theorem Comp_elim x y (K:Ens->Prop) (K_sound: SoundPred K)
: IN x (Comp y K) -> (IN x y /\ K x).
Proof.
intro e.
split.
+ exact ((Comp_INC y K) _ e).
+ apply IN_Comp_P in e. exact e.
  intros.
  eapply K_sound.
  exact H.
  exact H0.
Defined.

Theorem Comp_elimC x y (K:class) : IN x (Comp y K) -> (IN x y /\ K x).
Proof.
apply Comp_elim.
(** exact (sound_transf _ (sound K)). **)
intros a b q aeqb.
eapply (sound K).
exact aeqb.
exact q.
Defined.

Definition cInter (c:class) : class.
Proof.
unshelve eapply Build_class'.
{ intro e. exact (forall z:Ens, c z -> IN e z). }
{ simpl. intros a b aeqb czainz z cz.
  eapply IN_sound_left.
  exact aeqb.
  exact (czainz z cz). }
Defined.

Theorem InterEmpty : cEQ (cInter cE) cV.
Proof.
intro z. split; intro w.
+ simpl in * |- *. constructor.
+ simpl in * |- *. intros z0 [].
Defined.

Theorem InterSS (c:class) (x:Ens) (H : c x) :
 forall g, (cInter c) g -> (IN g x).
Proof.
simpl.
intros g K.
apply (K x H).
Defined.

(* set to class *)
Definition stoc : Ens -> class.
Proof.
intro x.
unshelve eapply Build_class'.
+ intro y. exact (IN y x).
+ (*intros a b aeqb.
  apply two_sided.*)
  intros a0 b0 H H0.
  eapply IN_sound_left. exact H. exact H0.
Defined.

Coercion stoc : Ens >-> class.

Theorem EQ2cEQ (a b : Ens) (aeqb : EQ a b) : cEQ a b.
Proof.
unfold cEQ.
eapply (axExt_right a b aeqb).
Defined.


Theorem eqv_rtran (T:Type) (A B C : T->Prop)
(H1:forall z : T, A z <-> B z)
(H2:forall z : T, A z <-> C z)
   :forall z : T, C z <-> B z.
Proof.
intro z. split; intro K.
+ apply (proj1 (H1 z)).
  apply (proj2 (H2 z)).
  assumption.
+ apply (proj1 (H2 z)).
  apply (proj2 (H1 z)).
  assumption.
Defined.

Theorem stoc_sound (e:Ens) : cEQ e (stoc e).
Proof.
intro z.
simpl in *|-*.
firstorder.
Defined.

Lemma sound2rewr (s:class) : forall w1 w2 : Ens, s w1 -> EQ w1 w2 -> s w2.
Proof.
intros w1 w2 H1 H2.
eapply (sound s). exact H2. exact H1.
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
    eapply (sound s). exact H. exact K.
    (** rewrite <- (sound s). exact K. exact H. **)
    (*apply (rewr _ _  K H).*)
  * exact y.
  * exact u.
+ intro u.
  apply (IN_Comp_P m).
  apply sound2rewr.
  exact u.
Defined.
(* try the same proof through the powerset *)

Theorem InterNonEmpty (c:class) (x:Ens) (H : c x) : ias (cInter c).
Proof.
eapply scosias.
eapply InterSS.
exact H.
Defined.

Definition cInd : class.
Proof.
unshelve eapply Build_class'.
+ exact Ind.
+ intros a b aeqb [Q0 Q1]. split.
  * eapply IN_sound_right. exact aeqb. exact Q0.
  * intros Y H.
    eapply IN_sound_right. exact aeqb.
    apply Q1. eapply IN_sound_right.
    apply EQ_sym. exact aeqb.
    exact H.
Defined.

Definition cUnion (c:class) : class.
Proof.
unshelve eapply Build_class'.
{ intro e. exact (exists z:Ens, c z /\ IN e z). }
{ simpl. intros a b aeqb [z [cz ainz]].
  exists z. split.
  +  exact cz.
  +  eapply IN_sound_left.
     exact aeqb.
     exact ainz. }
Defined.

(* Unionclass extends unionset *)
Theorem UCextendsUS (e:Ens) (c:class) (p:cEQ e c)
: cEQ (Union e) (cUnion c).
Proof.
intro z; split; intro H.
+ apply Union_IN in H as [y [H1 H2]].
  simpl in * |- *.
  exists y.
  split.
  - unfold cEQ in p.
    apply (proj1 (p y)).
    assumption.
  - exact H2.
+ simpl in * |- *.
  destruct H as [w [P1 P2]].
  eapply IN_Union.
  2 : { exact P2. }
  unfold cEQ in p.
  apply (proj2 (p w)).
  exact P1.
Defined.

(* Class of all subsets *)
Definition cPower (c:class) : class.
Proof.
unshelve eapply Build_class'.
{ intro e.
  exact (forall w, IN w e -> c w).
}
{ simpl.
  intros a b aeqb H.
  intros z K.
  apply H.
  eapply IN_sound_right.
  apply EQ_sym, aeqb.
  assumption. }
Defined.

(* The powerclass of V equals V. *)
Theorem PVeqV : cEQ (cPower cV) cV.
Proof.
intro z. split; intro H.
+ simpl. constructor.
+ simpl. simpl in H.
intros. constructor.
Defined.

(* Powerclass of set is a powerset of set. *)
Theorem PCextendsPS (e:Ens) (c:class) (p:cEQ e c)
: cEQ (Power e) (cPower c).
Proof.
intro z. split; intro H.
+ simpl in * |- *.
  intros w winz.
  apply IN_Power_INC in H.
  unfold cEQ in p.
  apply (proj1 (p w)) in H.
  exact H.
  exact winz.
+ simpl in * |- *.
  apply INC_IN_Power.
  intros w winz.
  unfold cEQ in p.
  apply (proj2 (p w)).
  exact (H w winz).
Defined.

Theorem Power_extends (e:Ens) : cEQ (Power e) (cPower e).
Proof.
intro z. split; intro H.
+ simpl in * |- *.
  intros w winz.
  apply IN_Power_INC in H.
  apply H.
  exact winz.
+ simpl in * |- *.
  apply INC_IN_Power.
  intros w winz.
  apply H.
  exact winz.
Defined.


Lemma schSepar_lem (c:class) :
forall w1 w2 : Ens, c w1 -> EQ w1 w2 -> c w2.
Proof.
intros w1 w2 cw1 eqw1w2.
eapply (sound c). exact eqw1w2. exact cw1.
(** rewrite (sound c).
exact cw1.
apply EQ_sym; assumption. **)
Defined.

Theorem schSepar (c:class) :
forall X:Ens, exists Y:Ens, forall z, (IN z Y <-> IN z X /\ (prty c z)).
Proof.
intros X.
exists (Comp X c).
intro z; split; intro H.
+ pose (H':=H).
  apply IN_Comp_P in H'.
  - eapply Comp_INC in H.
    firstorder.
  - apply schSepar_lem.
+ apply IN_P_Comp.
  - apply schSepar_lem.
  - firstorder.
  - firstorder.
Defined.

Definition cOmega := cInter cInd.

(* Omega is inductive set 
TODO: redefine Omega using set-theoretic approach.
*)
Theorem Omega_cInd : cInd Omega.
Proof.
constructor.
+ unfold Omega. simpl. exists 0. apply EQ_refl.
+ intros Y H.
apply IN_Omega_EXType in H.
destruct H as [n p].
unshelve eapply IN_sound_left.
exact (Class_succ (Nat n)).
try apply Class_succ_sound. 
exact p.
simpl.
exists (S n).
apply EQ_refl.
Defined.

Theorem nat_is_set: ias cOmega.
Proof.
unfold cOmega.
unshelve eapply InterNonEmpty.
exact Omega.
try apply Omega_cInd.
Defined.

(* Equality of conglomerates *)
Definition EQK (k1 k2 : class -> Prop)
 := forall (c:class), k1 c <-> k2 c.

(* "is a class" predicate on conglomerates *)
Definition iac (k:class -> Prop) : Prop.
Proof.
exact (forall (c:class), (k c) -> (ias c)).
Defined.

Section sec_ex2sig.
(*Context (ex2sig:forall (A:Type) (P:A->Prop), @ex A P -> @sig A P).*)
Definition ctos (c:class) (H:ias c) : Ens.
Proof.
apply ex2sig in H.
destruct H.
exact x.
Defined.
End sec_ex2sig.

Definition ktoc (k:class -> Prop) (H:iac k) : class.
Proof.
unshelve eapply Build_class'.
{ intro e.
  exact (exists c:class, k c  /\ k c ).
}
Abort.

(* OTHER POSSIBLE DEFINITIONS OF "iac"
exact (exists (m:class),
 forall (c:class), (exists (w:Ens), m ) <-> (k c)
).
exact (exists (m:class), forall (w:Ens), m w <-> (k (stoc w))).
*)

(* UNDER CONSTRUCTION *)



Definition axExtC (x y:Ens) : EQ x y <-> cEQ x y
 := (axExt x y).

(* New comprehension *)
Definition Compr : Ens -> class -> Ens.
Proof.
intros e c.
exact (Comp e c).
Defined.

Definition cComp : class -> class -> class.
Proof.
intros A B.
unshelve eapply Build_class'.
+ intro e. exact (A e /\ B e).
+ simpl. intros.
  (* apply EQ_sym in H. *)
  firstorder.
  - eapply (sound). exact H. exact H0.
  - eapply (sound). exact H. exact H1.
Defined.

(* Transitive closure *)
Definition trcl : Ens -> Ens.
Proof.
intro x.
eapply Inter.
eapply Comp.
Admitted. (* we need transfinite recursion *)

Theorem trcl_tran (y:Ens) 
: forall x:Ens, IN x (trcl y) -> INC x (trcl y).
Proof.
Admitted.

Theorem trcl_subs (y:Ens) : INC y (trcl y).
Proof.
Admitted.

(* Gödel stated regularity for classes rather than for
sets in his 1940 monograph, which was based on lectures
given in 1938. In 1939, he proved that regularity for
 sets implies regularity for classes. see  Kanamori 2009 *)
(* ST p.64, Lemma 6.2 *)
Definition caxReg : forall T : class,
       (exists a : Ens, T a ) ->
       exists y : Ens, T y /\ ~ (exists z : Ens, IN z y /\ T z).
Proof.
intros T [x Tx].
pose (t:=trcl (Sing x)).
pose (X:=Comp t T).
assert (inhX:exists x':Ens, IN x' X).
+ exists x. unfold X.
(* OR change X with (Comp t T). (*replace X with (Comp t T).*)*)
apply IN_P_Comp.
- intros. eapply (sound T). exact H0. exact H.
  (*apply sound_transf.
  exact (sound T).*)
- unfold t.
  apply trcl_subs.
  apply IN_Sing.
- exact Tx.
+ apply axReg in inhX as [t0 [P1 P2]].
  exists t0. split.
  unfold X in P1.
  - apply IN_Comp_P in P1. exact P1.
    intros. eapply (sound T). exact H0. exact H.
    (** apply sound_transf; exact (sound T). **)
  - intros [z [zinu Tz]]. apply P2.
    exists z. split. exact zinu.
    unfold X in P1 |-*.
    apply IN_P_Comp.
    *  intros. eapply (sound T). exact H0. exact H.
(** apply sound_transf; exact (sound T). **)
    * assert (t0inct: INC t0 t).
      {intros q W.
       apply Comp_elim in P1 as [t0int Tt0].
       assert(K:=trcl_tran _ _ t0int).
       apply K.
       assumption.
       unfold SoundPred.
intros. eapply (sound T). exact H0. exact H.
       (** apply sound_transf; exact (sound T). **)
      }
      apply t0inct.
      exact zinu.
    * exact Tz.
Defined.

(*Search Comp.*)

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
unshelve eapply Build_class'.
intro z.
exact (exists (x y:Ens), (EQ z (OrdPair x y)) /\ X x /\ Y y).
(*apply two_sided.*)
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
 : IN (Pair r1 r2) (Power R).
Proof.
apply INC_IN_Power.
intros z H.
apply Pair_IN in H as [H|H];
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
 (Power (Power (Union (Pair X1 X2))))
.
Proof.
intros X1 X2 a H.
pose (H1 := H).
destruct H1 as [x1 [x2 [A [B1 B2]]]].
simpl in B1, B2.

pose (Q:=Power (Power (Union (Pair X1 X2)))).
fold Q.
change _ with (IN a Q).
apply INC_IN_Power.
intros s1 U1.
apply INC_IN_Power.
intros s2 U2.
apply IN_sound_right with (1:=A) in U1.
apply Pair_IN in U1 as [V1|V2].
+ apply IN_Union with (E':=X1).
  apply IN_Pair_left.
  apply IN_sound_right with (1:=V1) in U2.
  apply IN_Sing_EQ, EQ_sym in U2.
  apply IN_sound_left with (1:=U2), B1.
+ apply IN_sound_right with (1:=V2) in U2.
  apply Pair_IN in U2 as [c1|c2].
  - apply IN_Union with (E':=X1).
    apply IN_Pair_left.
    apply EQ_sym in c1.
    eapply IN_sound_left with (1:=c1).
    exact B1.
  - apply IN_Union with (E':=X2).
    apply IN_Pair_right.
    apply EQ_sym in c2.
    eapply IN_sound_left with (1:=c2).
    exact B2.
Defined.


(*_________________________________*)

(* (n+1)th power of A *)
Fixpoint cp1Pow (A:class) (n:nat) : class :=
match n with
 | O => A
 | S x => cProduct (cp1Pow A x) A 
end.

(* Relations *)
Definition sound'
     : forall (c : class) (a b : Ens),
       EQ a b -> c a <-> c b.
Proof.
intros. split. eapply (sound c). exact H.
eapply (sound c). apply EQ_sym. exact H.
Defined.

Definition cDom (R:class) : class.
Proof.
unshelve eapply Build_class'.
intro u.
exact (exists v, R (OrdPair u v)).
(*apply two_sided.*)
intros a b aeqb H.
destruct H as [x w].
exists x.
rewrite (sound' R).
exact w.
apply OrdPair_sound_left.
auto with zfc. (*apply EQ_sym; exact aeqb.*)
Defined.

Definition exampleproperclass : class.
Proof.
Abort.

(*Definition ias (s: class) : Prop.*)
(* Proof. firstorder. (* Show Proof. *) . Defined. *)

Definition cprty_sound (cprty:class->Prop) (A B: class)
(w:cEQ A B) (H:cprty A): cprty B.
Proof. unfold cEQ in w. firstorder. (*impossible*) Abort.

(* ToDo: Find unsound class property. *)
Definition cprty_unsound : exists (cprty : class->Prop) 
(A B : class) (w : cEQ A B) (HA : cprty A) (HB : cprty B), False.
Proof. Abort.





(* Cartesian product of sets is a set. *)
Theorem cpss (x y : Ens) : ias (cProduct x y).
Proof.
eapply scosias.
intros z H.
apply prodissc.
exact H.
Defined.

(* Cartesian product as an operation on sets *)
Definition CProduct (x y:Ens): Ens.
Proof.
exact (Compr (Power (Power (Union (Pair x y)))) (cProduct x y)).
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

Ltac ueapp P := unshelve eapply P.

Lemma cEQ_refl (x:class): cEQ x x.
Proof.
intros m; reflexivity.
Defined.

Lemma cEQ_symm (x y:class): cEQ x y -> cEQ y x.
Proof.
intros H m. symmetry. apply H.
Defined.

Lemma cEQ_tran (x y z:class): cEQ x y -> cEQ y z -> cEQ x z.
Proof.
intros H1 H2 m.
transitivity (y m).
apply H1. apply H2.
Defined.


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
  apply nothing_IN_Vide in J as [].
+ apply B in C.
  apply nothing_IN_Vide in C as [].
Defined.

Theorem union_vide: EQ (Union Vide) Vide.
Proof.
apply axExt.
intro z. split; intro H.
+ apply Union_IN in H as [w [W1 W2]].
  destruct (nothing_IN_Vide w W1).
+ destruct (nothing_IN_Vide z H).
Defined.

Lemma nemp_then_inh (S:Ens) (H:~EQ S Vide) : exists m, IN m S.
Proof.
unshelve eapply not_all_not_ex.
intro D.
apply H.
apply (empty_set_EQ_Vide S).
exact D.
Defined.

Lemma pi1pi2 (E:Ens): E = sup (pi1 E) (pi2 E).
Proof.
destruct E.
apply f_equal.
apply functional_extensionality.
intro. simpl. reflexivity.
Defined.

Lemma pi1pi2' (E:Ens): EQ E (sup (pi1 E) (pi2 E)).
Proof.
destruct E. simpl. 
split; intro z; exists z; auto with zfc.
Defined.

Lemma lem3 (S:Ens) (K:~IN Vide S) :
forall a:Ens, IN a S -> exists b:Ens, IN b a.
Proof.
intros a ainS.
 pose (f:=classic (EQ a Vide)).
 destruct f as [J|J].
 eapply IN_sound_left in ainS.
 2 : exact J.
 destruct (K ainS).
 apply nemp_then_inh.
 exact J.
Defined.

Theorem lem4 (S:Ens) (a:pi1 S) : IN (pi2 S a) S.
Proof.
induction S.
simpl.
exists a.
apply EQ_refl.
Defined.

Lemma in2term (s x:Ens) : IN x s -> (pi1 s).
Proof. intro xins. destruct s. simpl in xins.
apply ex2sig in xins.
destruct xins as [y ep]. 
exact y.
Defined.

Lemma goodlem (b US:Ens) (binUS:IN b US) : EQ b (pi2 US (in2term US b binUS)).
Proof.
unfold in2term.
destruct US.
simpl.
simpl in binUS.
destruct (ex2sig binUS). (* A (fun y : A => EQ b (e y)) *)
assumption.
Defined.

Theorem OrdPair_sound_both :
  forall x1 x2 y1 y2: Ens, 
EQ x1 x2 -> EQ y1 y2 -> EQ (OrdPair x1 y1) (OrdPair x2 y2).
Proof.
intros x1 x2 y1 y2 x1eqx2 y1eqy2.
eapply EQ_tran.
eapply OrdPair_sound_left.
exact x1eqx2.
eapply OrdPair_sound_right.
exact y1eqy2.
Defined.

Section AC_sec.
Context (S:Ens).
Context (H:~IN Vide S).

Definition AC_A:=pi1 S.
Definition AC_B:=pi1 (Union S).
Definition AC_T:AC_A->AC_B->Prop 
 := fun a b => IN (pi2 (Union S) b) (pi2 S a).
(*Definition AC_P:= fun ts tus => IN (pi2 (Union S) tus) (pi2 S ts).*)
Theorem AC_hyp : forall a : AC_A, (exists b : AC_B, AC_T a b).
Proof.
intro a.
unfold AC_A, AC_B, AC_T in *|-*.
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

Definition AC_R : AC_A->AC_A->Prop := fun a1 a2 => EQ (pi2 S a1) (pi2 S a2).

Theorem AC_eqvR : RelationClasses.Equivalence AC_R.
Proof.
constructor.
+ intro x. apply EQ_refl.
+ intros x1 x2 K. apply EQ_sym. exact K.
+ intros x1 x2 x3 K1 K2. eapply EQ_tran. exact K1. exact K2.
Defined.

Theorem T_sound : (forall (x x' : AC_A) (y : AC_B),
 AC_R x x' -> AC_T x y -> AC_T x' y).
Proof.
intros x1 x2 y Rx1x2 Txy.
eapply IN_sound_right.
exact Rx1x2.
exact Txy.
Defined.

(*Axiom (SFC:SetoidFunctionalChoice_on AC_A AC_B).*)
Definition SFC:= axSFC AC_A AC_B.

Definition Afp := ex2sig (SFC AC_R AC_T AC_eqvR T_sound AC_hyp).
Definition Afu := fun v : pi1 S =>
 OrdPair (pi2 S v) (pi2 (Union S) ((proj1_sig Afp) v)).
Definition Achfu : Ens := (sup (pi1 S) Afu).

(*Search Power.*)

Theorem Achfu_total (X:Ens) (G:IN X S): exists Q, IN (OrdPair X Q) Achfu /\ IN Q X.
Proof.
pose (t:=in2term S X G).
pose (p:=Afu t).
(*&pose (p:=t). *)
unfold Afu in p.
exists (pi2 (Union S) (proj1_sig Afp t)).
split.
(*exists p.*)
{ unfold Achfu.
  unfold IN.
exists t. (*!*)
unfold t.

apply OrdPair_sound_both.
apply goodlem.
apply EQ_refl. }
{ 
pose (Y:= proj2_sig Afp t).
unfold AC_T in Y.
destruct Y as [Y1 Y2].
eapply IN_sound_right.
2 :  exact Y1.
unfold t.
apply EQ_sym.
apply goodlem. }
Defined.

Lemma eq2EQ (E1 E2:Ens) (K:E1=E2): EQ E1 E2.
Proof. destruct K. apply EQ_refl. Defined.

Theorem Achfu_func : forall X:Ens, (IN X S) ->
(forall Q1 Q2, IN (OrdPair X Q1) Achfu /\ IN (OrdPair X Q2) Achfu -> EQ Q1 Q2).
Proof.
intros X W Q1 Q2 [K1 K2].
unfold Achfu, IN in K1,K2.
unfold Afu in K1,K2.
destruct K1 as [y1 K1], K2 as [y2 K2].
(*Search OrdPair.*)
apply OrdPair_inj in K1 as [L1 R1].
apply OrdPair_inj in K2 as [L2 R2].
eapply EQ_tran. exact R1.
eapply EQ_tran. 2 : { apply EQ_sym. exact R2. }
pose (J:=(proj2_sig Afp)).

apply eq2EQ.
apply f_equal.

simpl in J. unfold AC_T in J.
destruct (J y1) as [_ QR].
apply (QR y2).
unfold AC_R.
eapply EQ_tran. apply EQ_sym. exact L1. exact L2.
Defined.

Theorem axChoice : exists f:Ens,
forall X, IN X S -> (* '<->' for the restriction of f on S *)
((exists Q, IN (OrdPair X Q) f /\ IN Q X) /\
 (forall Q1 Q2, IN (OrdPair X Q1) f /\ IN (OrdPair X Q2) f -> EQ Q1 Q2)).
Proof.
exists Achfu.
intros X.
 intro G.
+ split.
  - (* totality of the relation: existence of the ordered pair *)
    apply Achfu_total with (1:=G).
  - (* functionality of the relation *)
    apply Achfu_func with (1:=G).
Defined.

End AC_sec.

Definition uniqueEns : (Ens -> Prop) -> Ens -> Prop 
:= fun (P : Ens -> Prop) (x : Ens) =>
   P x /\ (forall x' : Ens, P x' -> EQ x x').

(* Projections for ordered pairs. *)
Definition Pi1 (p : Ens) : Ens
:= Union (Inter p).

Definition Pi2_P (p:Ens) := (fun x => 
~(EQ (Union p) (Inter p))->~(IN x (Inter p)) ).

(* Projections for ordered pairs. *)
Definition Pi2 (p : Ens) : Ens
:= Union (Comp (Union p) (Pi2_P p)).

Theorem Pi1_sound (X Y: Ens) (H: EQ X Y): EQ (Pi1 X) (Pi1 Y).
Proof.
unfold Pi1.
apply Union_sound.
apply Inter_sound.
exact H.
Defined.

Theorem EQ_sound X1 X2 Y1 Y2 (H1: EQ X1 Y1) (H2: EQ X2 Y2)
 (H: EQ X1 X2): EQ Y1 Y2.
Proof.
apply (EQ_tran _ X1).
auto with zfc.
apply (EQ_tran _ X2); auto with zfc.
Defined.

Theorem Pi2_sound_lem1 (X: Ens) : forall w1 w2 : Ens,
Pi2_P X w1 -> EQ w1 w2 -> Pi2_P X w2.
(*(~ EQ (Union X) (Inter X) -> ~ IN w1 (Inter X)) ->
EQ w1 w2 -> ~ EQ (Union X) (Inter X) -> ~ IN w2 (Inter X).*)
Proof.
 intros w1 w2 H0 H1 H2 H3.
  apply (IN_sound_left w2 w1) in H3.
  2 : auto with zfc.
  apply H0; assumption.
Defined.

Theorem Pi2_sound_lem2 (X Y : Ens) (H : EQ X Y) :
forall w : Ens, (Pi2_P X w) <-> (Pi2_P Y w).
(*(~ EQ (Union X) (Inter X) -> ~ IN w (Inter X)) <->
(~ EQ (Union Y) (Inter Y) -> ~ IN w (Inter Y)).*)
Proof.
intro w. revert X Y H.
  apply two_sided.
  intros X Y H  L0 L1 L2.
  apply L0.
  - intro L3. apply L1.
    apply (EQ_sound (Union X) (Inter X)).
    3 : assumption.
    apply Union_sound, H.
    apply Inter_sound, H.
  - eapply (IN_sound_right _ (Inter Y)).
    apply Inter_sound, EQ_sym, H.
    exact L2.
Defined.

Theorem Pi2_sound (X Y: Ens) (H: EQ X Y): EQ (Pi2 X) (Pi2 Y).
Proof.
unfold Pi2.
apply Union_sound.
apply Comp_sound.
3 : apply Union_sound; exact H.
+ apply Pi2_sound_lem1.
+ apply (Pi2_sound_lem2 X Y H).
Defined.

Theorem InterOP A B : EQ (Inter (OrdPair A B)) (Sing A).
Proof.
apply axExt_left.
intro z. split; intro q.
+ apply (IN_Inter_all (OrdPair A B) z q (Sing A)).
  unfold OrdPair.
  auto with zfc.
+ apply (all_IN_Inter (OrdPair A B) z (Sing A)).
  unfold OrdPair.
  auto with zfc.
  intros E H.
  apply IN_Sing_EQ in q.
  apply Pair_IN in H as [H|H].
  - apply (IN_sound_left A).
    auto with zfc.
    apply (IN_sound_right _ (Sing A)).
    auto with zfc.
    auto with zfc.
  - apply (IN_sound_right _ (Pair A B)).
    auto with zfc.
    apply (IN_sound_left A).
    auto with zfc.
    auto with zfc.
Defined.

Theorem UnionOP A B : EQ (Union (OrdPair A B)) (Pair A B).
Proof.
apply axExt_left.
intro z. split; intro q.
+ apply Union_IN in q as [E [q0 q1]].
  apply Pair_IN in q0 as [q2|q2].
  - apply IN_sound_right with (1:=q2) in q1.
    apply IN_Sing_EQ in q1.
    eapply IN_sound_left.
    1 : apply EQ_sym, q1.
    apply IN_Pair_left.
  - eapply IN_sound_right. exact q2. exact q1.
+ eapply IN_Union.
  2 : exact q.
  unfold OrdPair.
  auto with zfc.
Defined.

(* computation of Pi1 *)
Theorem Pi1_comput (A B:Ens): EQ (Pi1 (OrdPair A B)) A.
Proof.
unfold Pi1.
apply (EQ_tran _ (Union (Sing A))).
+ apply Union_sound.
  apply InterOP.
+ apply unionsing.
Defined.

Lemma contrap {A B:Prop}: (~A->~B)->(B->A).
Proof.
intros. destruct (classic A).
exact H1.
destruct (H H1 H0).
Defined.

(* computation of Pi2 *)
Theorem Pi2_comput (A B:Ens): EQ (Pi2 (OrdPair A B)) B.
Proof.
unfold Pi2.
apply axExt. intro z. split; intro q.
+ (* -> *)
apply Union_IN in q as [w [q1 q2]].
eapply Comp_elim in q1 as [q3 q4].
2 : { unfold SoundPred.
intros.
eapply (Pi2_sound_lem1 _ w1); assumption.
}
unfold Pi2_P in q4.
apply Union_IN in q3 as [E1 [q5 q6]].
assert (q7:=contrap q4); clear q4.
Search Pair.
apply Pair_IN in q5 as [q8|q8].
- eapply IN_sound_right in q6. 2 : exact q8.
  assert (q9:IN w (Inter (OrdPair A B))).
  { eapply IN_sound_right.
    apply EQ_sym, InterOP. assumption. }
  assert (q10:=q7 q9).
  assert (q11:= EQ_tran _ _ _  q10 (InterOP A B)).
  apply EQ_sym in q11.
  assert (q12:= EQ_tran _ _ _  q11 (UnionOP A B)).
  apply SingEqPair in q12 as [_ q12].

  apply IN_Sing_EQ in q6.
  eapply IN_sound_right with (1:=q12).
  eapply IN_sound_right with (1:=q6).
  exact q2.
- eapply IN_sound_right in q6. 2 : exact q8.
  apply Pair_IN in q6 as [q6|q6].
  2 : {eapply IN_sound_right. exact q6. exact q2. }
  (* the next is a copy *)
    assert (q9:IN w (Inter (OrdPair A B))).
  { eapply IN_sound_right.
    apply EQ_sym, InterOP.
    eapply IN_sound_right.
    apply Sing_sound. exact q6.
    apply IN_Sing. }
  assert (q10:=q7 q9).
  assert (q11:= EQ_tran _ _ _  q10 (InterOP A B)).
  apply EQ_sym in q11.
  assert (q12:= EQ_tran _ _ _  q11 (UnionOP A B)).
  apply SingEqPair in q12 as [_ q12].
  eapply IN_sound_right with (1:=q12).
  eapply IN_sound_right with (1:=q6).
  exact q2.
+ eapply IN_Union.
  2 : exact q.
  apply IN_P_Comp.
  - apply Pi2_sound_lem1.
  - eapply IN_Union.
    2 : apply IN_Pair_right.
    apply IN_Pair_right.
  - unfold Pi2_P.
    intros q1 q2; apply q1; clear q1. (*apply anticontrap.*)
    eapply EQ_tran.
    apply UnionOP.
    apply EQ_sym.
    eapply EQ_tran.
    apply InterOP.
    apply Pair_sound. apply EQ_refl.
    eapply IN_sound_right in q2.
    2 : apply InterOP.
    apply IN_Sing_EQ in q2.
    apply EQ_sym, q2.
Defined.

(* http://us.metamath.org/mpegif/df-iota.html *)
Definition riota (X S:Ens) (P:Ens->Prop) : Ens
 := Union (Comp X (fun y : Ens => EQ (Comp S P) (Sing y))).
(*Proof.
apply Union.
eapply Comp.
+ exact X.
+ intro y.
  apply EQ.
  - apply Comp.
    exact S.
    exact P.
  - exact (Sing y).
Defined.*)

(* http://us.metamath.org/mpegif/df-fv.html *)
Definition AT (F: Ens) (X:Ens) : Ens.
Proof.
(*intros F A.*)
Check riota.
Admitted.

(*(AT f Vide)*)
Theorem AT_sound_right (F X Y:Ens) (H:EQ X Y)
: EQ (AT F X) (AT F Y).
Proof.
Abort.

(*** Recursion theorem ***)
(* IST p.46 *)
Theorem rec_thm (a A g:Ens) (H1:IN a A) 
(H2: IN g (functions (Product A Omega) A)) 
: ex (uniqueEns (fun f:Ens=>
   IN f (functions Omega A) /\
   (EQ (AT f Vide) a) /\
   forall n:Ens, IN n Omega ->
    EQ (AT f (Class_succ n)) (AT g
     (OrdPair (AT f n) n)
    )
  )).
Proof.
(*unique
exists ().
(*ex (unique ... )*)
constructor.
"exists!"*)
Abort.

Definition collection :=
  forall P : Ens -> Ens -> Prop,
  (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) ->
  (forall E : Ens, ex (P E)) ->
  forall E : Ens,
  (exists A : Ens,
     forall x : Ens, IN x E -> (exists y : Ens, IN y A /\ P x y)).


Definition choice :=
  forall (A B : Type) (P : A -> B -> Prop),
  (forall a : A, (exists b : B, P a b)) ->
  (exists f : A -> B, forall a : A, P a (f a)).

Theorem thm_choice : choice.
Proof.
intros A B P H.
assert (J0:RelationClasses.Equivalence (@eq A)).
{ constructor; auto.
  intros x y z xeqy yeqz.
  induction xeqy. exact yeqz. }
assert (J1:(forall (x x' : A) (y : B), x = x' -> P x y -> P x' y)).
{ intros x x' y xeqx'. induction xeqx'. trivial. }
(*Check (axSFC A B (@eq A) P J0 J1 H).*)
destruct (axSFC A B (@eq A) P J0 J1 H) as [f Q].
exists f. firstorder.
Defined.

Theorem Choice_Collection : choice -> collection.
Proof.
unfold collection in |- *; intro; intros P comp G E.
cut ((exists f : Ens -> Ens, forall B : Ens, P B (f B))).
simple induction 1; intros f pf.
elim E; intros A g hr; intros.
exists (sup A (fun a : A => f (g a))).
simpl in |- *; intros X i.
elim i; intros a ea.
exists (f (g a)).
split.
exists a; auto with zfc.
apply comp with (g a); auto with zfc.
unfold choice in H.
apply H; intros.
elim (G a); intros b hb; exists b; auto with zfc.
Defined.

Theorem thm_collection : collection.
Proof. apply Choice_Collection. exact thm_choice. Defined.

(* If we also assume the excluded middle, we can derive         *)
(* the usual replacement schemata.                              *)

Definition functional (P : Ens -> Ens -> Prop) :=
  forall x y y' : Ens, P x y -> P x y' -> EQ y y'.

Definition replacement :=
  forall P : Ens -> Ens -> Prop,
  functional P ->
  (forall x y y' : Ens, EQ y y' -> P x y -> P x y') ->
  (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) ->
  forall X : Ens,
  (exists Y : Ens,
     forall y : Ens,
     (IN y Y -> (exists x : Ens, IN x X /\ P x y)) /\
     ((exists x : Ens, IN x X /\ P x y) -> IN y Y)).

Theorem classical_Collection_Replacement :
 (forall S : Prop, S \/ (S -> False)) -> collection -> replacement.
Proof.
unfold replacement in |- *; intros EM Collection P fp comp_r comp_l X.
cut
 ((exists Y : Ens,
     forall y : Ens, (exists x : Ens, IN x X /\ P x y) -> IN y Y)).
simple induction 1; intros Y HY.
exists (Comp Y (fun y : Ens => (exists x : Ens, IN x X /\ P x y))).
intros y; split.
intros HC.
apply
 (IN_Comp_P Y y
    (fun y0 : Ens => (exists x : Ens, IN x X /\ P x y0)));
 auto with zfc.
intros w1 w2; simple induction 1; intros x; simple induction 1;
 intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
intros He.
apply IN_P_Comp.

intros w1 w2; simple induction 1; intros x; simple induction 1;
 intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
apply HY; auto with zfc.
auto with zfc.

elim
 (Collection
    (fun x y : Ens =>
     P x y \/ (forall y' : Ens, P x y' -> False) /\ EQ y Vide)) 
  with X.
intros Y HY.
elim (EM ((exists x : Ens, IN x X /\ P x Vide))).
intros Hvide; elim Hvide; intros xv Hxv; exists Y.
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
elim (HY x Hx1).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2.
intros Hy'3; apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
simple induction 1; intros Hy'3 Hy'4.
elim (Hy'3 y Hx2).
intros HP; exists (Comp Y (fun y : Ens => EQ y Vide -> False)).
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
apply IN_P_Comp.
intros w1 w2 Hw1 Hw Hw2; apply Hw1; apply EQ_tran with w2; auto with zfc.
elim (HY x).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2; intros Hy'3.
apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
elim Hy'3; intros Hy'4 Hy'5.
elim (Hy'4 y); auto with zfc.
assumption.
intros e; apply HP; exists x; split; auto with zfc; apply comp_r with y;
 auto with zfc; apply fp; auto with zfc.
intros x x' y e Hx; elim Hx; intros Hx1.
left; apply comp_l with x; auto with zfc.
right; elim Hx1; intros Hx2 Hx3; split.
2: assumption.
intros y' Hy'; apply (Hx2 y'); apply comp_l with x'; auto with zfc.
intros x; elim (EM ((exists y : Ens, P x y))); intros Hx.
elim Hx; intros x0 Hx0; exists x0; left; assumption.
exists Vide; right; split; auto with zfc.
intros y Hy; elim Hx; exists y; auto with zfc.
Defined.

Theorem thm_replacement : replacement.
Proof.
apply classical_Collection_Replacement.
exact classic.
exact thm_collection.
Defined.


(* ===================================== *)
(*    START OF THE METAMATH SECTION      *)
(* ===================================== *)

Lemma cEQ_sym A B : cEQ A B -> cEQ B A.
Proof. intros H w. split.
exact (proj2 (H w)).
exact (proj1 (H w)).
Defined.

Lemma cEQ_sound_left (A1 A2 B: class) (H : cEQ A1 A2)
(K : cEQ A1 B) : cEQ A2 B.
Proof.
unfold cEQ in K|-*.
intro z.
split; intro q.
+ apply K. apply H. exact q.
+ apply H. apply K. exact q.
Defined.

Lemma cEQ_sound_right (A B1 B2: class) (H : cEQ B1 B2)
(K : cEQ A B1) : cEQ A B2.
Proof.
unfold cEQ in K|-*.
intro z.
split; intro q.
+ apply H. apply K. exact q.
+ apply K. apply H. exact q.
Defined.


Lemma two_sided3 (D:class->class) :
(forall A B : class, cEQ A B -> forall z : Ens, (D A) z -> (D B) z)
->
(forall A B : class, cEQ A B -> cEQ (D A) (D B)).
Proof.
intros. intro q. split.
+ apply H. exact H0.
+ apply H. apply cEQ_sym. exact H0.
Defined.

Definition cIN (A B:class):Prop := exists x:Ens, cEQ x A /\ B x.

Theorem cIN_sound_left (A1 A2 B:class) (H:cEQ A1 A2)
 (K:cIN A1 B) : cIN A2 B.
Proof.
unfold cEQ, cIN in *|-*.
destruct K as [x [P1 P2]].
exists x. split.
+ eapply cEQ_sound_right.
  exact H.
  exact P1.
+ exact P2.
Defined.

Coercion EQ2cEQ : EQ >-> cEQ .

Definition cPair : class -> class -> class.
Proof.
intros A B.
unshelve eapply Build_class'.
+ intro e. exact ((cEQ e A)\/(cEQ e B)).
+ intros a b aeqb.
  simpl. intros [H|H].
  - left. eapply cEQ_sound_left. exact aeqb. exact H.
  - right. eapply cEQ_sound_left. exact aeqb. exact H.
Defined.

Definition cSing (A:class) : class := cPair A A.

(* http://us.metamath.org/mpegif/df-op.html *)
Definition cOrdPair (A B:class):class.
Proof.
unshelve eapply Build_class'.
+ intro x. exact (cIN A cV /\ cIN B cV /\
  cIN x (cPair (cSing A) (cPair A B))
 ).
+ simpl.
  intros a b aeqb [P1 [P2 P3]].
  repeat split; try assumption.
  eapply cIN_sound_left.
  - apply EQ2cEQ.
    exact aeqb.
  - exact P3.
Defined.

Lemma two_sidedC (P:class->class) :
(forall (B1 B2 : class) (H : cEQ B1 B2),
forall z : Ens, (P B1) z -> (P B2) z)
->
forall (B1 B2 : class) (H : cEQ B1 B2), cEQ (P B1) (P B2)
.
Proof.
intros.
split; apply H.
+ assumption.
+ apply cEQ_sym. assumption.
Defined.

Theorem cPair_sound_right (A B1 B2:class) (H:cEQ B1 B2) :
 cEQ (cPair A B1) (cPair A B2).
Proof.
revert B1 B2 H.
apply two_sidedC.
intros.
  simpl in *|-*.
  destruct H0 as [M|M].
  - left. exact M.
  - right.
    eapply (cEQ_sound_right).
    * exact H.
    * exact M.
Defined.

Theorem cPair_sound_left (A1 A2 B:class) (H:cEQ A1 A2) :
 cEQ (cPair A1 B) (cPair A2 B).
Proof.
revert A1 A2 H.
apply two_sidedC.
intros.
  simpl in *|-*.
  destruct H0 as [M|M].
  - left.
    eapply (cEQ_sound_right).
    2 : exact M.
    exact H.
  - right.
    exact M.
Defined.

Theorem cPair_sound (A1 A2 B1 B2:class) (HA:cEQ A1 A2)
(HB:cEQ B1 B2) : cEQ (cPair A1 B1) (cPair A2 B2).
Proof.
eapply cEQ_tran.
+ eapply cPair_sound_left. exact HA.
+ eapply cPair_sound_right. exact HB.
Defined.

Theorem cIN_sound_right (Z B1 B2 : class)
(H : cEQ B1 B2) (K : cIN Z B1) : cIN Z B2.
Proof.
(*revert B1 B2 H K.
apply (two_sidedC _ ).*)
unfold cIN in *|-*.
destruct K as [x [P1 P2]].
exists x. split.
+ exact P1.
+ assert (Hx:=H x).
  apply proj1 in Hx.
  apply Hx.
  exact P2.
Defined.

Theorem cOrdPair_sound_right (A B1 B2:class) (H:cEQ B1 B2):
 cEQ (cOrdPair A B1) (cOrdPair A B2).
Proof.
revert B1 B2 H.
apply (two_sidedC _ ).
intros.
simpl in *|-*.
destruct H0, H1. (*hack instead of repeat destruct H0.*)
repeat split.
+ assumption.
+ eapply cIN_sound_left.
  exact H.
  exact H1.
+ eapply cIN_sound_right. 
2 : exact H2.
apply cPair_sound_right.
apply cPair_sound_right.
exact H.
Defined.

Theorem cSing_sound (A1 A2:class) (H:cEQ A1 A2) :
 cEQ (cSing A1) (cSing A2).
Proof.
unfold cSing.
eapply cPair_sound; exact H.
Defined.

Theorem cOrdPair_sound_left (A1 A2 B:class) (H:cEQ A1 A2) :
 cEQ (cOrdPair A1 B) (cOrdPair A2 B).
Proof.
revert A1 A2 H. apply two_sidedC.
intros.
simpl in *|-*.
destruct H0, H1. (*hack instead of repeat destruct H0.*)
repeat split.
+ eapply cIN_sound_left.
  exact H.
  exact H0.
+ assumption.
+ eapply cIN_sound_right.
  2 : exact H2.
  eapply cPair_sound.
  eapply cSing_sound. exact H.
  eapply cPair_sound_left. exact H.
Defined.

Definition cINC (A B:class) : Prop := forall x:Ens, A x -> B x.

(* http://us.metamath.org/mpegif/df-tr.html *)
Definition Tr (A:class) : Prop := cINC (cUnion A) A.

Theorem cUnion_sound : forall (A B : class) (aeqb : cEQ A B),
 cEQ (cUnion A) (cUnion B).
Proof.
unfold cEQ.
apply two_sided3.
intros.
simpl in *|-*.
destruct H0 as [w [P1 P2]].
exists w. split. 2:exact P2.
apply H. assumption.
Defined.

Theorem Tr_sound (A B : class) (aeqb : cEQ A B) : (Tr A) -> (Tr B).
Proof.
unfold Tr in *|-*.
unfold cINC.
intros.
try eapply cUnion_sound in H0.
2 : exact aeqb.
apply aeqb.
apply H.
assumption.
Defined.

(* predicate of the nonemptiness TODO: make class *)
Definition inhab (x:Ens) : Prop := exists y:Ens, IN y x.

(* "Fr" is the well-founded relation predicate.
http://us.metamath.org/mpegif/df-fr.html *)
Definition Fr (R A:class) : Prop :=
forall x:Ens, ((forall y, IN y x -> A y) /\ inhab x) ->
exists y, IN y x /\ forall z, IN z x -> ~ (cIN (cOrdPair z y) R).

Definition IrrR (R A:class) : Prop :=
 forall x, A x -> ~ cIN (cOrdPair x x) R.

Theorem IrrR_sound_right (R A B:class)
 (p:cEQ A B) (H:IrrR R A):IrrR R B.
Proof.
unfold IrrR in *|-*.
intros x H0.
apply H. apply p. exact H0.
Defined.

Definition TranR (R A:class) : Prop :=
 forall x, A x ->
 forall y, A y ->
 forall z, A z -> 
 (cIN (cOrdPair x y) R /\ cIN (cOrdPair y z) R -> cIN (OrdPair x z) R)
.

Theorem TranR_sound_right (R A B:class)
 (p:cEQ A B) (H:TranR R A):TranR R B.
Proof.
unfold TranR in *|-*.
intros x Bx y By z Bz.
apply H; apply p; assumption.
Defined.

(* the strict partial order predicate
 similar with http://us.metamath.org/mpegif/df-po.html *)
Definition Po (R A:class) : Prop := (IrrR R A)/\(TranR R A)
.

Theorem Po_sound_right (R A B:class)
 (p:cEQ A B) (H:Po R A):Po R B.
Proof.
unfold Po in *|-*.
destruct H as [H1 H2].
split.
+ eapply IrrR_sound_right.
  exact p.
  exact H1.
+ eapply TranR_sound_right.
  exact p.
  exact H2.
Defined.


(* strict complete (linear) order predicate 
 similar with http://us.metamath.org/mpegif/df-so.html *)
Definition Or (R A:class) : Prop := Po R A /\
(forall x, A x -> forall y, A y ->
(cIN (OrdPair x y) R \/ EQ x y \/ cIN (cOrdPair y x) R)
).

Theorem Or_sound_right (R A B:class)
 (p:cEQ A B) (H:Or R A):Or R B.
Proof.
unfold Or in *|-*.
destruct H as [H1 H2].
split.
eapply Po_sound_right.
exact p.
exact H1.
intros x Qx y Qy.
apply p in Qx.
apply p in Qy.
exact (H2 x Qx y Qy).
Defined.

(* http://us.metamath.org/mpegif/df-we.html *)
Definition We (R A:class) : Prop := (Fr R A /\ Or R A).

Theorem Fr_sound_right (R A B:class)
 (p:cEQ A B) (H:Fr R A):Fr R B.
Proof.
unfold Fr in *|-*.
intros.
assert (M:(forall y : Ens, IN y x -> A y) /\ inhab x).
{ destruct H0 as [L1 L2].
  split. 2:exact L2.
  intros y yinx. apply p. apply L1. exact yinx. }
destruct (H x M) as [y [yinx P]].
exists y.
split. exact yinx.
intros z zinx Rp.
eapply P.
exact zinx.
exact Rp.
Defined.

Theorem We_sound_right (R A B:class)
 (p:cEQ A B) (H:We R A):We R B.
Proof.
unfold We in *|-*.
destruct H as [H1 H2].
split.
+ eapply Fr_sound_right.
  exact p.
  exact H1.
+ eapply Or_sound_right.
  exact p.
  exact H2.
Defined.

(*
Opaque EQ. (* forbid "simpl" to unfold "EQ" *) Transparent EQ.
The following also disables simpl, but EQ can still be unfolded.
*)
Arguments EQ _ _ : simpl nomatch.

(* TODO: EQ_sound_left *)


(* http://us.metamath.org/mpegif/df-eprel.html *)
Definition cEps : class.
Proof.
unshelve eapply Build_class'.
+ intro p. exact (exists x y:Ens, cEQ p (cOrdPair x y) /\ IN x y).
+ intros a b aeqb.
  simpl. intros [x [y [aeqxy xiny]]].
  exists x. exists y. split.
  - eapply cEQ_sound_left. apply EQ2cEQ.
    exact aeqb. exact aeqxy.
  - exact xiny.
Defined.

(* http://us.metamath.org/mpegif/df-ord.html *)
Definition Ord (A:class) : Prop := (Tr A /\ We cEps A).

Definition Ord_sound (A B:class) (AeqB:cEQ A B) (H:Ord A) : Ord B.
Proof.
unfold Ord in *|-*.
destruct H as [TrA WeEA].
split.
+ eapply Tr_sound. exact AeqB. exact TrA.
+ eapply We_sound_right. exact AeqB. exact WeEA.
Defined.

Theorem Ord_esound : forall a b : Ens, EQ a b -> Ord a -> Ord b.
Proof.
intros a b aeqb.
apply Ord_sound.
apply EQ2cEQ.
assumption.
Defined.

(* ordinal numbers *)
Definition On : class.
Proof.
unshelve eapply Build_class'.
+ intro x. exact (Ord x).
+ simpl. exact Ord_esound.
Defined.

Definition Rel (A:class) : Prop := cINC A (cProduct cV cV).

Theorem EQ_sound_left (a b c : Ens) (aeqb : EQ a b) 
 (H : EQ a c) : EQ b c.
Proof.
apply EQ_sym in aeqb.
eapply EQ_tran.
exact aeqb.
exact H.
Defined.

(* http://us.metamath.org/mpegif/df-cnv.html *)
Definition invR (A:class) : class.
Proof.
unshelve eapply Build_class'.
+ intro e.
  exact (exists x y:Ens, cEQ e (cOrdPair x y) /\ cIN (cOrdPair y x) A).
+ intros a b aeqb. simpl.
  intros [x [y [W1 W2]]].
  exists x. exists y.
  split.
  eapply cEQ_sound_left. apply EQ2cEQ.
  exact aeqb.
  exact W1.
  exact W2.
Defined.

(* composition *)
Definition compos (A B:class):class.
Proof.
unshelve eapply Build_class'.
+ intro e.
exact (exists x y, cEQ e (cOrdPair x y) /\
 exists z, cIN (cOrdPair x z) B /\ cIN (cOrdPair z y) A
).
+ simpl. intros a b aeqb [x [y [aeq P]]].
  exists x. exists y. split. 2:exact P.
  eapply cEQ_sound_left. apply EQ2cEQ.
  exact aeqb.
  exact aeq.
Defined.

Definition cI : class.
Proof.
unshelve eapply Build_class'.
+ intro e. exact (exists x:Ens, cEQ e (cOrdPair x x)).
+ simpl. intros a b aeqb [x p].
  exists x. eapply cEQ_sound_left. exact aeqb.
  exact p.
Defined.

(* http://us.metamath.org/mpegif/df-fun.html *)
Definition Fun (A:class): Prop 
 := (Rel A) /\ (cINC (compos A (invR A)) cI).

(* Check cIN.
Context (Q1 Q2:class).
Parameter ap : forall A : class, class -> Prop.
Coercion  : ap >-> Funclass.
Parameter ap : forall A B:Set, class -> class -> Prop.
Coercion cIN : class >-> Funclass.
Check Q1 Q2. *)

(* http://us.metamath.org/mpegif/df-dm.html *)
Definition cdom (A:class) : class.
Proof.
unshelve eapply Build_class'.
+ intro e. exact (exists y, cIN (cOrdPair e y) A).
+ simpl. intros a b aeqb [y Aop].
  exists y.
  (*eapply (sound' A).*)
  eapply cIN_sound_left.
  2 : exact Aop.
  apply cOrdPair_sound_left.
  apply EQ2cEQ.
  apply  aeqb.
Defined.

(* http://us.metamath.org/mpegif/df-fn.html *)
Definition Fn (A B:class): Prop := (Fun A)/\(cEQ (cdom A) B).

(* here we use "F:class" instead of "ph:wff" *)
Definition iota_cl (F:class) : class.
Proof.
unshelve eapply Build_class'.
+ intro y. exact (cEQ F (cSing y)).
+ simpl.
(*
pose (W:=sound (cSing F)).
unfold cSing in W.
simpl in W.
  unfold cEQ in *|-*.
Check fun a b =>.
*)
intros a b aeqb; intro H.
  intro z. assert (H:=H z).
  destruct H as [H1 H2]. split.
  - intro Fz. assert (H1:=H1 Fz).
    destruct H1 as [L|L]; left.
    * eapply cEQ_sound_right.
       exact aeqb. exact L.
    * eapply cEQ_sound_right.
      apply EQ2cEQ. exact aeqb. exact L.
  - intros [zheqb|zheqb]; apply H2; left.
    * eapply cEQ_sound_right. apply EQ2cEQ, EQ_sym.
      exact aeqb. exact zheqb.
    * eapply cEQ_sound_right. apply EQ2cEQ, EQ_sym.
      exact aeqb. exact zheqb.
(* TODO: reduce repetitions! *)
Defined.

(* http://us.metamath.org/mpegif/df-iota.html *)
Definition iota (F:class) : class
 := cUnion (iota_cl F).



(*  Show Proof.
IN_sound_left

eapply cIN_sound_right. (*TODO!*)
unfold cEQ.

unfold cOrdPair.
fold cPair.
apply cPair_sound_right.
Admitted.*)

(* http://us.metamath.org/mpegif/df-fv.html *)
Definition cAT (F:class) (A:class) : class.
Proof.
apply iota.
unshelve eapply Build_class'.
+ intro x. exact (cIN (cOrdPair A x) F).
+ simpl.
  intros a b aeqb.
  apply cIN_sound_left.
  apply cOrdPair_sound_right.
  apply EQ2cEQ.
  exact aeqb.
Defined.

(* Later, change every soundness proof with this.
   keeping "<->" for "rewrite" tactic is useless. *)
Definition soundf : forall (c : class) (a b : Ens),
       EQ a b -> c a -> c b.
Proof.
intros.
apply (sound c a b H).
exact H0.
Defined.

Lemma cINC_sound_left (A1 A2 B:class) (H:cEQ A1 A2) (K:cINC A1 B) : cINC A2 B.
Proof.
intros z P.
apply K.
apply H.
exact P.
Defined.

Lemma Rel_sound (A1 A2:class) (H:cEQ A1 A2) (K:Rel A1) : Rel A2.
Proof.
unfold Rel in *|- *.
eapply cINC_sound_left.
exact H.
exact K.
Defined.

Lemma compos_sound_left : forall (B A1 A2:class) (H:cEQ A1 A2),
 cEQ (compos A1 B) (compos A2 B).
Proof.
intros.
eapply (two_sidedC (fun z => (compos z B))).
2 : exact H.
intros.
rename z into e. (*cbn delta in H1.*)
simpl in H1|-*.
destruct H1 as [x [y [zeqp [z [P1 P2]]]]].
exists x.
exists y.
split. exact zeqp.
exists z.
split. exact P1.
eapply cIN_sound_right.
apply H0.
exact P2.
Defined.

Lemma compos_sound_right : forall (A B1 B2:class) (H:cEQ B1 B2),
 cEQ (compos A B1) (compos A B2).
Proof.
intro A.
eapply (two_sidedC (compos A)).
intros.
rename z into e.
simpl in H0|-*.
destruct H0 as [x [y [zeqp [z [P1 P2]]]]].
exists x.
exists y.
split. exact zeqp.
exists z.
split.
eapply cIN_sound_right.
apply (H). exact P1.
exact P2.
Defined.

Lemma compos_sound (A1 A2 B1 B2:class) (HA:cEQ A1 A2) (HB:cEQ B1 B2) : 
 cEQ (compos A1 B1) (compos A2 B2).
Proof.
eapply cEQ_tran.
apply compos_sound_left. exact HA.
apply compos_sound_right. exact HB.
Defined.

Lemma invR_sound : forall (A1 A2:class) (H:cEQ A1 A2),
 cEQ (invR A1) (invR A2).
Proof.
eapply (two_sidedC (invR)).
intros.
simpl in H0|-*.
destruct H0 as [x [y [P1 P2]]].
exists x. exists y. split. exact P1.
eapply cIN_sound_right.
apply H. exact P2.
Defined.

Lemma Fun_sound (A1 A2:class) (H:cEQ A1 A2) (K:Fun A1) : Fun A2.
Proof.
unfold Fun in *|- *.
destruct K.
split.
+ eapply Rel_sound. exact H. exact H0.
+ eapply cINC_sound_left. 2 : exact H1.
  apply compos_sound.
  exact H.
  apply invR_sound.
  exact H.
Defined.


Lemma cdom_sound : forall (A1 A2 : class) (H : cEQ A1 A2),
  cEQ (cdom A1) (cdom A2).
Proof.
eapply (two_sidedC).
simpl.
intros.
destruct H0 as [y P].
exists y.
eapply cIN_sound_right. apply H. exact P.
Defined.

Lemma Fn_sound_left (A1 A2 B:class) (H:cEQ A1 A2) (K:Fn A1 B) : Fn A2 B.
Proof.
destruct K.
split.
eapply Fun_sound.
exact H. exact H0.
eapply cEQ_sound_left.
2 :  exact H1.
apply cdom_sound.
exact H.
Defined.

Lemma cAT_sound_left (B:class) : forall (A1 A2:class) (H:cEQ A1 A2),
  cEQ (cAT A1 B) (cAT A2 B).
Proof.
eapply (two_sidedC).
intros. simpl in H0|-*.
destruct H0 as [w [P1 P2]].
exists w.
split.
+ eapply cEQ_sound_left.
  2 : exact P1.
  unfold cEQ.
  simpl.
  intro q. split; intro g.
  - eapply cIN_sound_right.
    exact H. exact g.
  - eapply cIN_sound_right.
    apply cEQ_sym. exact H. exact g.
+ exact P2.
Defined.

(* wff   ->  Prop
   set   ->  Ens
   class ->  class *)

(* Constructing the class of an acceptable functions. *)
Definition cAccept (F:class) : class.
Proof.
unshelve eapply Build_class'.
+ intro f.
  refine (exists x:Ens, On f /\ (Fn f x /\ forall y:Ens, IN y x
    -> cEQ (cAT f y) (cAT F y)
  )).
+ intros.
  cbv beta in H0|-*.
  destruct H0 as [x [P1 [P2 P3]]].
  exists x.
  split. 2 : split.
  - eapply soundf.
    exact H. exact P1.
  - eapply Fn_sound_left.
    apply EQ2cEQ. exact H. exact P2.
  - intros y yinx. 
    eapply cEQ_sound_left.
    2 : exact (P3 y yinx).
    eapply cAT_sound_left.
    apply EQ2cEQ. exact H.
Defined.

(* http://us.metamath.org/mpegif/df-recs.html *)
(* transfinite recursion "functor". *)
Definition recs (F:class) := cUnion (cAccept F).

(* LEM implies proof irrelevance:
   see proof_irrelevance in Classical_Prop.v *)

(* http://us.metamath.org/mpegif/df-iun.html *)
Definition iun (A:class) (B:Ens->class) : class. (*A:Ens->class*)
Proof.
unshelve eapply Build_class'.
+ intro y. exact (exists x, A x /\ (B x) y).
+ simpl. intros a b aeqb [x [P1 P2]].
  exists x. split. exact P1.
  eapply (sound (B x)). exact aeqb. exact P2.
Defined.

(* http://us.metamath.org/mpegif/uniiun.html *)
Theorem uniiun (A:class): cEQ (cUnion A) (iun A (id)).
Proof.
intro z.
simpl.
split; intro q.
+ destruct q as [w [P1 P2]].
  exists w. split. exact P1.
  exact P2. (* compute. ? *)
+ destruct q as [w [P1 P2]].
  exists w. split. exact P1.
  exact P2.
Defined.

(* http://us.metamath.org/mpegif/reliun.html *)
Theorem reliun (A:class) (B:Ens->class) :
 Rel (iun A B) <-> (forall x, A x -> Rel (B x)).
Proof.
split; intro H.
+ intros x Ax.
  unfold Rel in H|-*.
  intros z Bx.
  apply (H z).
  simpl.
  exists x. split; assumption.
+ unfold Rel in H|-*.
  intros z Bx.
  simpl in Bx.
  destruct Bx as [x [Ax Bxz]].
  eapply H.
  exact Ax.
  exact Bxz.
Defined.
(* TODO: define "-->" - functions which respect extensional equality. *)

(* http://us.metamath.org/mpegif/reluni.html *)
Theorem reluni (A:class) : (Rel (cUnion A)) <-> (forall x, A x -> Rel x).
Proof.
split; intro H1.
+ eapply Rel_sound in H1.
  2 : apply uniiun.
  unfold id in H1.
  apply reliun.
  exact H1.
+ eapply Rel_sound.
  apply cEQ_sym.
  apply uniiun.
  unfold id.
  apply reliun.
  exact H1.
Defined.

(* http://us.metamath.org/mpegif/tfr1.html *)
Theorem recs_is_rel (F:class) : Rel (recs F).
Proof.
unfold recs.
apply reluni.
simpl.
intros x H.
destruct H as [A [OrdA [FnxA P]]].
unfold Fn in FnxA.
unfold Fun in FnxA.
destruct FnxA as [[Q _] _].
exact Q.
Defined.

(* http://us.metamath.org/mpegif/zfpair2.html *)
Lemma Pair_extends (x y:Ens): cEQ (Pair x y) (cPair x y).
Proof.
intro w. split; simpl; intro H.
+ destruct H as [[|] J].
  - left. exact J.
  - right. exact J.
+ destruct H as [H|H].
  - exists true. apply axExtC. exact H.
  - exists false. apply axExtC. exact H.
Defined.

Lemma Pair_exists (x y:Ens): exists a:Ens, cEQ a (cPair x y). 
Proof.
exists (Pair x y). apply Pair_extends.
Defined.

(* http://us.metamath.org/mpegif/prex.html *)
Lemma cPair_exists (A B:class): exists a:Ens, cEQ a (cPair A B).
Proof.
destruct (classic (exists a : Ens, cEQ a A) ) as [[a ae]|],
         (classic (exists b : Ens, cEQ b B) ) as [[b be]|].
+ exists (Pair a b).
  unshelve eapply cEQ_sound_right.
  exact (cPair a b).
  2 : apply Pair_extends.
  eapply cPair_sound.
  exact ae.
  exact be.
+ exists (Sing a).
  unshelve eapply cEQ_sound_right.
  exact (cSing a).
  2 : apply Pair_extends.
  intro w. split; intro q.
  - simpl in *|-*.
    left. destruct q.
eapply cEQ_sound_right. exact ae. exact H0.
eapply cEQ_sound_right. exact ae. exact H0.
  - simpl in *|-*.
    destruct q. 
left. eapply cEQ_sound_right. apply cEQ_sym. exact ae. exact H0.
apply (ex_intro (fun w:Ens=>cEQ w B)) in H0. destruct (H H0).
+ exists (Sing b).
  unshelve eapply cEQ_sound_right.
  exact (cSing b).
  2 : apply Pair_extends.
  intro w. split; intro q.
  - simpl in *|-*.
    right. destruct q.
eapply cEQ_sound_right. exact be. exact H0.
eapply cEQ_sound_right. exact be. exact H0.
  - simpl in *|-*.
    destruct q.
apply (ex_intro (fun w:Ens=>cEQ w _)) in H0. destruct (H H0).
left. eapply cEQ_sound_right. apply cEQ_sym. exact be. exact H0.
+ exists Vide.
  intro w. split; intro q.
  - destruct q as [[]].
  - destruct q.
    apply (ex_intro (fun w:Ens=>cEQ w _)) in H1. destruct (H H1).
    apply (ex_intro (fun w:Ens=>cEQ w _)) in H1. destruct (H0 H1).
Defined.

Lemma EnsInV (e:Ens) : cV e.
Proof.
simpl.
trivial.
Defined.

Lemma eq_then_InV (A:class) (w:Ens) (p:cEQ w A): cIN A cV.
Proof.
unfold cIN.
exists w. split. exact p. exact (EnsInV w).
Defined.

(*
"Our df-op 3902 was chosen because it often
 makes proofs shorter by eliminating unnecessary sethood hypotheses."
http://us.metamath.org/mpegif/dfopif.html
*)
Lemma cOrdPair_exists (A B:class): exists a:Ens, cEQ a (cOrdPair A B).
Proof.
destruct (cPair_exists A A) as [w1 P1].
destruct (cPair_exists A B) as [w2 P2].
destruct (cPair_exists w1 w2) as [w P].
destruct (classic (exists a : Ens, cEQ a A) ) as [[a ae]|],
         (classic (exists b : Ens, cEQ b B) ) as [[b be]|].
** exists w.
eapply cEQ_sound_right.
2 : exact P.
intro z.
simpl.
split.
+ intros Q.
  repeat split.
  eapply eq_then_InV. exact ae.
  eapply eq_then_InV. exact be.
unfold cIN.
  destruct Q as [L1|L2].
  - exists w1. split. apply cEQ_sym. exact L1.
    simpl. left. exact P1.
  - exists w2. split. apply cEQ_sym. exact L2.
    simpl. right. exact P2.
+
(* DEVELOPMENT *)
Admitted.
(*  eapply Pair_extends.
unfold cOrdPair.
exists (Pair a b). *)

Lemma invR_op C x y: cIN (cOrdPair x y) (invR C) -> cIN (cOrdPair y x) C.
Proof.
unfold cIN.
intros [a [P1 P2]].
destruct (cPair_exists y x) as [w P].
exists w.
split.
+ eapply cEQ_sound_right.
(*  eapply Pair_extends.
  try exists (cOrdPair y x).
  simpl. *)
  2 : exact P.
Admitted.

Theorem recs_is_fun (F:class) : Fun (recs F).
Proof.
unfold Fun. split. exact (recs_is_rel F).
intros q H.
destruct H as [x [y [eqxop [z [P1 P2]]]]].
apply invR_op in P1.
simpl.
assert (xias : ias x). admit.
assert (yias : ias y). admit.
unfold ias in xias,yias.
destruct xias as [xs xexs].
destruct yias as [ys yexs].
exists ys.

(*
exists y.
eapply EQ_sound_left.
apply EQ_sym. exact eqxop.
eapply OrdPair_sound_left.

simpl in P1.*)
Abort.
(*unfold compos in H.
cbv beta in H|-*.
simpl in *|-*.*)

(* http://us.metamath.org/mpegif/df-rdg.html *)
(* Definition rec (F I:class) := recs F. *)

(* ===================================== *)
(*     END OF THE METAMATH SECTION       *)
(* ===================================== *)



(** BEGINning of the tiny experiments with ensembles **)
Require Import ClassicalFacts.
Module ExperimentsWithEnsembles.
Axiom axPE:prop_extensionality.
Axiom axPI : proof_irrelevance.
Definition U := Ens.
Definition Ensemble := class. (*U -> Prop.*)
Definition In (A:Ensemble) (x:U) : Prop := A x.
Definition Included (B C:Ensemble) : Prop := forall x:U, In B x -> In C x.
Definition Same_set (B C:Ensemble) : Prop 
:= Included B C /\ Included C B.
Theorem Extensionality_Ensembles : forall A B:Ensemble, 
Same_set A B -> A = B.
Proof.
intros.
unfold Same_set,Included,In,U in H.
unfold Ensemble in A, B.
destruct A, B; simpl in *|-*.
assert (p1:prty0=prty1).
apply functional_extensionality.
intro x.
destruct H as [H1 H2].
+ apply axPE. split.
  - apply H1.
  - apply H2.
+ destruct p1. apply f_equal.
eapply functional_extensionality_dep.
intro x.
apply functional_extensionality_dep.
intro y.
eapply functional_extensionality.
intro p.
eapply functional_extensionality.
intro Hx.
eapply axPI.
Defined.
(*Require Import Coq.Sets.Ensembles.
Check Extensionality_Ensembles.
Axiom Extensionality_Ensembles : forall A B:Ensemble, 
Same_set A B -> A = B.
*)
End ExperimentsWithEnsembles.
(** END of the tiny experiments with ensembles **)



(** BEGIN: Formulas for automatization of soundness proofs. **)
Section Fo.
Definition SetVars := nat.

Definition cng (val:SetVars -> Ens)
 (xi:SetVars) (m:Ens) : SetVars -> Ens
 :=
 (fun r:SetVars =>
 match Nat.eqb r xi with
 | true => m
 | false => (val r)
 end).

Inductive Fo :=
 |In : SetVars -> SetVars -> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
 |Fora(x:SetVars)(f:Fo): Fo
 |Exis(x:SetVars)(f:Fo): Fo
.

Fixpoint foI (val:SetVars->Ens) (f:Fo) : Prop :=
match f with
 | In x y => IN (val x) (val y)
 | Bot => False
 | Conj f1 f2 => (foI val f1) /\ (foI val f2)
 | Disj f1 f2 => (foI val f1) \/ (foI val f2)
 | Impl f1 f2 => (foI val f1) -> (foI val f2)
 | Fora x f => (forall m:Ens, foI (cng val x m) f)
 | Exis x f => (exists m:Ens, foI (cng val x m) f)
end.

(* foI respects the pointwise
 extensional equality of valuations: *)
Theorem ptws val1 val2 (K:forall v, EQ (val1 v) (val2 v) )
 f : (foI val1 f) -> foI val2 f.
Proof.
revert val1 val2 K.
induction f;
intros val1 val2 K H;
 simpl in *|-*.
5 : { intro W.
      eapply IHf2. exact K.
      eapply H.
      eapply IHf1.
      { intro v. apply EQ_sym. apply K. }
      exact W.
    }
5 : {
  intro m.
  eapply IHf.
  2 : apply H.
  intro v.
  instantiate (1 := m).
  unfold cng.
  destruct (Nat.eqb v x).
  apply EQ_refl.
  apply K.
  }
5 : { destruct H as [m H].
      exists m.
  eapply IHf.
  2 : apply H.
  intro v.
  unfold cng.
  destruct (Nat.eqb v x).
  apply EQ_refl.
  apply K.
}
  + eapply IN_sound_left. apply K.
    eapply IN_sound_right. apply K.
    exact H.
  + exact H.
  + destruct H as [H1 H2]. split.
    - eapply IHf1. 2 : exact H1. exact K.
    - eapply IHf2. 2 : exact H2. exact K.
  + destruct H as [H1|H2].
    - left. eapply IHf1. 2 : exact H1. exact K.
    - right. eapply IHf2. 2 : exact H2.  exact K.
Defined.

(* Build a class: *)
Definition BC (f:Fo) : class.
Proof.
unshelve eapply Build_class'.
* intro e. exact (foI (fun _ => e) f).
* simpl.
intros.
eapply ptws.
2 : exact H0.
simpl.
intros _.
exact H.
Defined.

(*Check BC (Impl Bot Bot).  (* _V *)*)
Theorem all_in_V (x:Ens) : BC (Impl Bot Bot) x.
Proof.
simpl. trivial.
Defined.
(* \forall x, x \in y <->  (x=\varempty) *)
Definition Iff (f1 f2:Fo) := (Conj (Impl f1 f2) (Impl f2 f1)).

(*Definition Subs (x y:SetVars) : Fo
 := (Fora 9 (Impl (In 9 x) (In 9 y))).*)

(*Definition Eqs (x y:SetVars) : Fo
 := Conj (Subs x y) (Subs y x).*)

Definition Neg q := (Impl q Bot).

(* Let's define a singletone *)
Definition isEmpty (x:SetVars)
: Fo := (Fora 1 (Neg (In 1 x))).

Theorem Vide_isEmpty1 : (BC (isEmpty 7)) (Vide).
Proof.
simpl.
intros.
destruct H as [[]].
Defined.

Theorem Vide_isEmpty2 : (BC (isEmpty 1)) (Vide).
Proof.
simpl.
intros.
assert (K:IN m m). exact H.
eapply snis.
exact K.
Defined.

Theorem Vide_isEmpty3 n : (BC (isEmpty n)) (Vide).
Proof.
simpl.
intros.
unfold cng in H.
change (Nat.eqb 1 1) with true in H.
destruct (Nat.eqb n 1).
+ simpl in H.
  eapply snis.
  exact H.
+ eapply nothing_IN_Vide, H.
Defined.

Lemma no_choose A (b:bool) (c:A) : (if b then c else c) = c.
Proof. destruct b;reflexivity. Defined.

Theorem isEmpty_EQ_Sing_Vide
 : cEQ (BC (isEmpty 7)) (Sing Vide).
Proof.
intros x.
split; intros H.
+
simpl in *|-*.
exists true.
apply empty_set_EQ_Vide.
intros.
unshelve eapply H.
exact E'.
exact H0.
+
simpl in *|-*.
intros.
assert (W: IN m x).
apply H0.
destruct H.
rewrite (no_choose _ x0 Vide) in H.
eapply IN_sound_right in W.
2 : exact H.
eapply nothing_IN_Vide, W.
Defined.

(* Definition isOne (x:SetVars)
: Fo := (Fora 1 (Neg (In 1 x))).*) 

(*
Definition pair (BC (Fora 1 (In 1 2))) : .
Definition subclass (BC (Fora 1 (In 1 2))) : .
*)

(* TODO: Need to enrich the language.
cPair
cEQ_sound_left
Check BC (Impl Bot Bot).  (* _V *)
Theorem all_in_V (A B:class): c INC (BC (Conj 1 )).
Proof.
simpl. trivial.
Defined. *)

End Fo.
(** END: Formulas for automatization of soundness proofs. **)





(** TRASH SECTION **)
(*
Check 0.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
(*From VerifiedMathFoundations.library*)
Require Export PredicateCalculus.
Module PredicateCalculusClasses.

End PredicateCalculusClasses.
*)
(** END OF TRASH SECTION-**)