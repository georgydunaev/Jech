Theorem axInfty : exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n)).
Proof.
  exists (sup Nat (fun n:Nat => Nat n)).
  intro z; split; intro H.
  + apply IN_sup.
    exact H.
  + destruct H as [n fxz].
    apply IN_sup.
    exists n.
    exact fxz.
Qed.
