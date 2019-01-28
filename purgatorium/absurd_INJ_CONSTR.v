(* 
https://cstheory.stackexchange.com/questions/27943/law-of-excluded-middle-in-mltt
https://lists.chalmers.se/pipermail/agda/2010/001565.html *)
Inductive I : (Prop -> Prop) -> Prop := .

Axiom inj_I : forall x y, I x = I y -> x = y.

Definition R (x : Prop) := forall p, x = I p -> ~ p x.

Lemma R_eqv :
  forall p, R (I p) <-> ~ p (I p).

Proof.
split; intros.
 unfold R; apply H.
 reflexivity.
 unfold R; intros q H0.
 rewrite <- (inj_I p q H0).
 assumption.
Qed.

Lemma R_eqv_not_R :
  R (I R) <-> ~ R (I R).

Proof (R_eqv R).

Lemma absurd : False.

Proof.
destruct R_eqv_not_R.
exact (H (H0 (fun x => H x x)) (H0 (fun x => H x x))).
Qed.
