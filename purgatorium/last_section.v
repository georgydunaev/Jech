(************************* STOP HERE ****************************)


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

(* Other *)
Fixpoint nclass (n:nat) := 
match n with
| 0 => Ens
| S b => (nclass b)->Prop
end.
**********)