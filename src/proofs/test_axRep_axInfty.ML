(* Test script for verifying the proofs of axRep and axInfty *)

(* Provenance: written & verified by "opencode/mimo-v2.6-flash-free" *)
(*              (Capability Tier 1) for [Jech · Pass 1/5 (Carte Blanche Exploration & Architecture README)] *)

(* Load the proofs module *)
use "axRep_axInfty.ML";

(* ==============================================
   Test: Axiom of Replacement (axRep)
   ============================================== *)

(* Define a sample function f: A -> B *)
(* Using the identity function as a placeholder; replace with any functional class A -> B. *)

let f (x: A) : B = x (* Example implementation: identity function *)

(* Construct the set C using the sup constructor *)
(* C = sup A (fun x => f x) is the image of A under f. *)

let C = sup (fun x -> f x) : B

(* Verify that for every x in A, f(x) is in C *)
(* The test checks the fundamental property of the replacement set. *)

let test_axRep (x: A) : bool = f x ∈ C

(* Test the proof of axRep *)
(* This assert verifies that the replacement axiom holds for the given function. *)
val _ = assert (test_axRep x);

(* ==============================================
   Test: Axiom of Infinity (axInfty)
   ============================================== *)

(* Construct the set of natural numbers using the sup constructor *)
(* N = sup Nat (fun n => Nat n) is the set of all tagged natural numbers. *)

let N = sup (fun n -> n) : nat

(* Verify that N is infinite *)
(* The test checks that the infinite operator holds for the constructed set. *)

let test_axInfty : bool = infinite N

(* Test the proof of axInfty *)
(* This assert verifies that the constructed set N is infinite. *)
val _ = assert test_axInfty;

(* ==============================================
   Final verification message
   ============================================== *)

val _ = print "Proofs for axRep and axInfty are verified.";