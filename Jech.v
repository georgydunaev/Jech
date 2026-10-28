(* Jech.v - Documentation for the Jech Library *)

(* Examples and Cross-References *)

(* Example Section *)
(* Example 1: Using the Jech Library to Prove a Theorem *)
Require Import Jech.Theorems.
Theorem example_theorem : forall x, P x -> Q x.
Proof.
  intros x H.
  apply theorem1 in H.
  apply theorem2.
Qed.

(* Example 2: Applying a Definition *)
Require Import Jech.Definitions.
Definition example_definition := (fun x => x + 1).

(* Example 3: Using a Lemma *)
Require Import Jech.Lemmas.
Lemma example_lemma : forall x, R x -> S x.
Proof.
  intros x H.
  apply lemma1 in H.
  apply lemma2.
Qed.

(* Cross-Reference Section *)
(* Cross-Reference 1: Related Theorem *)
See Theorem theorem1 in Jech.Theorems.

(* Cross-Reference 2: Related Definition *)
See Definition definition1 in Jech.Definitions.

(* Cross-Reference 3: Related Lemma *)
See Lemma lemma1 in Jech.Lemmas.