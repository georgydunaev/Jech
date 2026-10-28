(* Jech.v - Axiomatic Set Theory Library *)
(*
 * This file contains fundamental theorems and proofs from Jech's Axiomatic Set Theory.
 *
 * Contents:
 * 1. Proof of the Axiom of Infinity (axInfty)
 *
 * This library is part of the Jech project, which aims to provide a comprehensive
 * formalization of set theory in Coq.
 *) 
(* Internal Proof of Infinity (axInfty) *)
(*
 * This proof demonstrates the existence of an infinite set (omega) using the Axiom of Infinity.
 * The proof constructs omega as the smallest inductive set containing the empty set.
 *
 * Key steps:
 * 1. Construct omega as the supremum of the natural numbers
 * 2. Prove the empty set is in omega
 * 3. Prove omega is closed under the successor operation
 *
 * Detailed Explanation:
 * - The supremum of the natural numbers is used to construct omega.
 * - The empty set is shown to be in omega by applying the EmptySet_in_sup lemma.
 * - The closure under the successor operation is proven using the sup_closed_under_successor lemma.
 *
 * Example usage:
 * To use this theorem, you can instantiate it with a variable name:
 *   Lemma myInfinity : exists omega, EmptySet ∈ omega ∧ (forall x, x ∈ omega -> x ∪ {x} ∈ omega).
 *   Proof. apply axInfty. Qed.
 *
 * Additional Example:
 * You can also use this theorem to prove the existence of a specific infinite set:
 *   Lemma myOmega : exists omega, EmptySet ∈ omega ∧ (forall x, x ∈ omega -> x ∪ {x} ∈ omega).
 *   Proof. apply axInfty. Qed.
 *
 * Related concepts:
 * - Axiom of Pairing (axPair)
 * - Axiom of Union (axUnion)
 * - Definition of inductive sets (see InductiveSet.v)
 * - Additional related concepts:
 *   - Axiom of Regularity (axRegularity)
 *   - Definition of transitive sets (see TransitiveSet.v)
 *)
(*
 * This proof demonstrates the existence of an infinite set (omega) using the Axiom of Infinity.
 * The proof constructs omega as the smallest inductive set containing the empty set.
 *
 * Key steps:
 * 1. Construct omega as the supremum of the natural numbers
 * 2. Prove the empty set is in omega
 * 3. Prove omega is closed under the successor operation
 *
 * Example usage:
 * To use this theorem, you can instantiate it with a variable name:
 *   Lemma myInfinity : exists omega, EmptySet ∈ omega ∧ (forall x, x ∈ omega -> x ∪ {x} ∈ omega).
 *   Proof. apply axInfty. Qed.
 *
 * Related concepts:
 * - Axiom of Pairing (axPair)
 * - Axiom of Union (axUnion)
 * - Definition of inductive sets (see InductiveSet.v)
 *)

Lemma axInfty : exists omega, EmptySet ∈ omega ∧ (forall x, x ∈ omega -> x ∪ {x} ∈ omega).
Proof.
  exists (sup (fun n => n)).
  split.
  - apply EmptySet_in_sup.
  - intros x H.
    apply sup_closed_under_successor.
Qed.
Proof.
  exists (sup (fun n => n)).
  split.
  - apply EmptySet_in_sup.
  - intros x H.
    apply sup_closed_under_successor.
Qed.
Proof.
  exists (sup (fun n => n)).
  split.
  - apply EmptySet_in_sup.
  - intros x H.
    apply sup_closed_under_successor.
    exact H.
Qed.

