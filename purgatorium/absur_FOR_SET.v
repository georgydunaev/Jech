(*https://lists.chalmers.se/pipermail/agda/2010/001565.html
-----------------------------------------------------

From this proof, I realized it can be applied to Set as well.

-----------------------------------------------------*)
Inductive I : (Set -> Set) -> Set := 
| i1 : I (fun x => x)
| i2 : I (fun x => x)
.

Axiom inj_I : forall x y, I x = I y -> x = y.

Definition R (x : Set) : Set := forall p: Set -> Set, x = I p -> p x -> False.

Lemma R_eqv_1 :
  forall p, R (I p) -> (p (I p) -> False).

Proof.
intros ? ?. 
  apply H. reflexivity.
Qed.

Lemma R_eqv_2 :
  forall p, (p (I p) -> False) -> R (I p).

intros.
 unfold R; intros q H0.
 rewrite <- (inj_I p q H0).
 assumption.
Qed.

Lemma R_eqv_not_R_1 :
  R (I R) -> R (I R) -> False.

Proof (R_eqv_1 R).

Lemma R_eqv_not_R_2 :
  (R (I R) -> False) -> R (I R).

Proof (R_eqv_2 R).

Lemma absurd : False.

Proof.
set (H := R_eqv_not_R_1).
set (H0 := R_eqv_not_R_2).

exact (H (H0 (fun x => H x x)) (H0 (fun x => H x x))).
Qed.