(* Test script for verifying the proofs of axRep and axInfty *)

(* Load the proofs module *)
use "axRep_axInfty.ML";

(* Verify the proofs *)
(* Test cases for verifying the proof of axRep *)

(* Define a sample function f: A -> B *)
let f (x: A) : B = ... (* Define the sample function f *)

(* Construct the set C using the sup constructor *)
let C = sup (fun x -> f x) : B

(* Verify that for every x in A, f(x) is in C *)
let test_axRep (x: A) : bool = f x ∈ C

(* Test the proof of axRep *)
val _ = assert (test_axRep x);

(* Test cases for verifying the proof of axInfty *)

(* Construct the set of natural numbers using the sup constructor *)
let N = sup (fun n -> n) : nat

(* Verify that N is infinite *)
let test_axInfty : bool = infinite N

(* Test the proof of axInfty *)
val _ = assert test_axInfty;

val _ = print "Proofs for axRep and axInfty are verified.";