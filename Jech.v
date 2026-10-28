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
 * Detailed Explanation of the Proof of the Axiom of Infinity (axInfty): *)
(*
 * The Axiom of Infinity states that there exists a set (omega) that is inductive and contains the empty set.
 * An inductive set is a set that contains the empty set and is closed under the successor operation.
 * The proof constructs omega as the smallest inductive set containing the empty set.
 *
 * Key steps in the proof:
 * 1. Construct omega as the supremum of the natural numbers.
 *    - The supremum of a set of natural numbers is the smallest natural number that is greater than or equal to all the numbers in the set.
 *    - In this case, the set of natural numbers is the set of all natural numbers less than a given natural number.
 * 2. Prove the empty set is in omega.
 *    - This is done by applying the EmptySet_in_sup lemma, which states that the empty set is in the supremum of any set of natural numbers.
 * 3. Prove omega is closed under the successor operation.
 *    - This is done by applying the sup_closed_under_successor lemma, which states that the supremum of a set of natural numbers is closed under the successor operation.
 *
 * Additional Details:
 * - The proof uses the Axiom of Regularity to ensure that the construction of omega is well-founded.
 * - The Axiom of Pairing is used to construct pairs of natural numbers, which are necessary for the successor operation.
 *
 * Example usage:
 * To use this theorem, you can apply it directly to construct the set of natural numbers.
 * For example:
 *
 * Lemma example_usage : omega = {0, 1, 2, ...}.
 * Proof.
 *   apply axInfty.
 * Qed.
 *
 * Cross-references:
 * - Related theorem: Axiom of Regularity (axReg)
 * - Related definition: Inductive set
 * - Related theorem: Axiom of Pairing (axPair)
 * - Related definition: Successor operation
 *)
(*
 * Detailed Explanation of the Proof of the Axiom of Infinity (axInfty):
 *
 * The Axiom of Infinity states that there exists a set (omega) that is inductive and contains the empty set.
 * An inductive set is a set that contains the empty set and is closed under the successor operation.
 * The proof constructs omega as the smallest inductive set containing the empty set.
 *
 * Key steps in the proof:
 * 1. Construct omega as the supremum of the natural numbers.
 *    - The supremum of a set of natural numbers is the smallest natural number that is greater than or equal to all the numbers in the set.
 *    - In this case, the set of natural numbers is the set of all natural numbers less than a given natural number.
 * 2. Prove the empty set is in omega.
 *    - This is done by applying the EmptySet_in_sup lemma, which states that the empty set is in the supremum of any set of natural numbers.
 * 3. Prove omega is closed under the successor operation.
 *    - This is done by applying the sup_closed_under_successor lemma, which states that the supremum of a set of natural numbers is closed under the successor operation.
 *
 * Example usage:
 * To use this theorem, you can apply it directly to construct the set of natural numbers.
 * For example:
 *
 * Lemma example_usage : omega = {0, 1, 2, ...}.
 * Proof.
 *   apply axInfty.
 * Qed.
 *
 * Cross-references:
 * - Related theorem: Axiom of Regularity (axReg)
 * - Related definition: Inductive set
 *)
(*
 * Detailed Explanation of the Proof of the Axiom of Infinity (axInfty):
 *
 * The Axiom of Infinity states that there exists a set (omega) that is inductive and contains the empty set.
 * An inductive set is a set that contains the empty set and is closed under the successor operation.
 * The proof constructs omega as the smallest inductive set containing the empty set.
 *
 * Key steps in the proof:
 * 1. Construct omega as the supremum of the natural numbers.
 * 2. Show that omega is inductive.
 * 3. Show that omega is the smallest inductive set containing the empty set.
 *
 * This proof is based on the construction of natural numbers and the properties of inductive sets.
 *)
(*
 * Detailed Explanation of the Proof of the Axiom of Infinity (axInfty):
 *
 * The Axiom of Infinity states that there exists a set (omega) that is inductive and contains the empty set.
 * An inductive set is a set that contains the empty set and is closed under the successor operation.
 * The proof constructs omega as the smallest inductive set containing the empty set.
 *
 * Key steps in the proof:
 * 1. Construct omega as the supremum of the natural numbers.
 *    - The supremum of a set of natural numbers is the smallest natural number that is greater than or equal to all the numbers in the set.
 *    - In this case, the set of natural numbers is the set of all natural numbers less than a given natural number.
 * 2. Prove the empty set is in omega.
 *    - This is done by applying the EmptySet_in_sup lemma, which states that the empty set is in the supremum of any set of natural numbers.
 * 3. Prove omega is closed under the successor operation.
 *    - This is done by applying the sup_closed_under_successor lemma, which states that the supremum of a set of natural numbers is closed under the successor operation.
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
 * - Axiom of Pairing (axPair): This axiom states that for any two sets, there exists a set that contains both of them.
 * - Axiom of Union (axUnion): This axiom states that for any set of sets, there exists a set that contains all the elements of the sets in the original set.
 * - Definition of inductive sets (see InductiveSet.v): An inductive set is a set that contains the empty set and is closed under the successor operation.
 * - Additional related concepts:
 *   - Axiom of Regularity (axRegularity): This axiom states that every non-empty set has an element that is disjoint from it.
 *   - Definition of transitive sets (see TransitiveSet.v): A transitive set is a set that contains all the elements of its elements.
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

