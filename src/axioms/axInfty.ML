(* Proof for axInfty using the sup constructor *)
(* ============================================================
 * Axiom of Infinity (axInfty)

(* Provenance: written & verified by "opencode/mimo-v2.6-flash-free" *)
(*              (Capability Tier 1) for [Jech · Pass 1/5 (Carte Blanche Exploration & Architecture README)] *)

(* Implementation of the proof for axInfty *)
 * ============================================================ *)
(* Statement: exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n))
 *
 * The Axiom of Infinity is constructed (not postulated) using the `sup`
 * constructor (Scott's sup-delta construction) with impredicative comprehension.
 * The set Y := sup Nat (fun n => Nat n) contains exactly the tagged
 * natural numbers as members — the analogue of ω in Jech Chapter 1.
 *
 * Key components:
 *   - Ens : the impredicative universe of sets-as-sup-trees
 *   - sup : supremum constructor, packs an index type A with a family f : A -> Ens
 *   - Nat : tagged constructor for natural-number atoms
 *   - EQ / IN : extensional equality and membership
 *
 * Proof outline:
 *   - Y := sup Nat (fun n => Nat n)
 *   - IN z (sup A f) unfolds to: exists a : A, EQ z (f a)
 *   - Injectivity of EQ on numerals: EQ (Nat n) (Nat m) <-> n = m
 *
 * This approach constructs ω impredicatively rather than postulating it,
 * contrasting with the classical ZFC axiom of infinity which postulates
 * an inductive set as an axiom.
 * ============================================================ *)

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
