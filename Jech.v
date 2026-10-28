(* Existing content from Jech.v *) + 
(* Internal Proof of Infinity (axInfty) *)

Lemma axInfty : exists omega, EmptySet ∈ omega ∧ (forall x, x ∈ omega -> x ∪ {x} ∈ omega).
Proof.
  exists (sup (fun n => n)).
  split.
  - apply EmptySet_in_sup.
  - intros x H.
    apply sup_closed_under_successor.
    exact H.
Qed.

