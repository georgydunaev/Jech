(* Heterogeneous equality *)
Definition hEQ (e:Ens) (c:class) :=
 forall z, IN z e <-> c z.

Theorem hEQ_sound_left (e1 e2:Ens) (p:EQ e1 e2) (c:class)
: (hEQ e1 c) -> (hEQ e2 c).
Proof.
intro H.
unfold hEQ in H|-*.
assert (j:=axExt_right e1 e2 p).
apply (eqv_rtran Ens _ _ _ H j).
Defined.

Theorem hEQ_sound_right (e:Ens) (c1 c2:class) (p:cEQ c1 c2)
: (hEQ e c1) -> (hEQ e c2).
Proof.
intro H.
unfold hEQ in H|-*.
unfold cEQ in p.
symmetry in H.
apply (eqv_rtran Ens _ _ _ p H).
Defined.

Theorem stoc_sound (e:Ens) : hEQ e (stoc e).
Proof.
intro z.
simpl in *|-*.
firstorder.
Defined.

(* Unionclass extends unionset *)
Theorem UCextendsUS (e:Ens) (c:class) (p:hEQ e c)
: hEQ (Union e) (cUnion c).
Proof.
intro z; split; intro H.
+ apply Union_IN in H as [y [H1 H2]].
  simpl in * |- *.
  exists y.
  split.
  - unfold hEQ in p.
    apply (proj1 (p y)).
    assumption.
  - exact H2.
+ simpl in * |- *.
  destruct H as [w [P1 P2]].
  eapply IN_Union.
  2 : { exact P2. }
  unfold hEQ in p.
  apply (proj2 (p w)).
  exact P1.
Defined.

(* Powerclass of set is a powerset of set. *)
Theorem PCextendsPS (e:Ens) (c:class) (p:hEQ e c)
: hEQ (Power e) (cPower c).
Proof.
intro z. split; intro H.
+ simpl in * |- *.
  intros w winz.
  apply IN_Power_INC in H.
  unfold hEQ in p.
  apply (proj1 (p w)) in H.
  exact H.
  exact winz.
+ simpl in * |- *.
  apply INC_IN_Power.
  intros w winz.
  unfold hEQ in p.
  apply (proj2 (p w)).
  exact (H w winz).
Defined.

Definition hPair : class -> class -> class.
Proof.
intros A B.
unshelve eapply Build_class'.
+ intro e. exact ((hEQ e A)\/(hEQ e B)).
+ intros a b aeqb.
  simpl. intros [H|H].
  - left. eapply hEQ_sound_left. exact aeqb. exact H.
  - right. eapply hEQ_sound_left. exact aeqb. exact H.
Defined.

Definition cIN (A B:class):Prop := exists x, hEQ x A /\ B x.