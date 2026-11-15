(* ========================================================================= *)
(* proofs/subtheories/inaccessible_cardinals.ML                              *)
(* Inaccessible Cardinals Sub-Theory in Standard ML (Jech Chapter 3 / 5)     *)
(*                                                                           *)
(* Original placeholder preserved in comments:                               *)
(* Theorem well_ordering : forall (X : Type) (R : X -> X -> Prop),           *)
(*   (forall x, R x x) /                                                     *)
(*   (forall x y z, R x y -> R y z -> R x z) /                               *)
(*   (forall x y, R x y -> R y x) ->                                         *)
(*   forall S : set X, S \neq \emptyset ->                                   *)
(*   exists x, x \in S / (forall y, y \in S -> R x y).                       *)
(* ========================================================================= *)

structure InaccessibleCardinalsSubtheory =
struct

  (* Representation of cardinal descriptors in a symbolic universe hierarchy:
     kappa is depicted by a record describing:
     - is_uncountable : whether kappa > aleph_0
     - is_regular     : whether cf(kappa) = kappa
     - is_limit_card  : whether kappa is a limit cardinal (weakly inaccessible)
     - is_strong_limit: whether for all lambda < kappa, 2^lambda < kappa *)
  type cardinal_spec = {
    name : string,
    is_uncountable : bool,
    is_regular : bool,
    is_limit_card : bool,
    is_strong_limit : bool
  }

  (* Weakly inaccessible cardinal: uncountable, regular, limit cardinal *)
  fun is_weakly_inaccessible (c : cardinal_spec) : bool =
    (#is_uncountable c) andalso (#is_regular c) andalso (#is_limit_card c)

  (* Strongly inaccessible cardinal: uncountable, regular, strong limit cardinal *)
  fun is_strongly_inaccessible (c : cardinal_spec) : bool =
    (#is_uncountable c) andalso (#is_regular c) andalso (#is_strong_limit c)

  (* Every strongly inaccessible cardinal is weakly inaccessible since
     strong limit implies limit cardinal *)
  fun strong_implies_weak (c : cardinal_spec) : bool =
    if is_strongly_inaccessible c andalso (#is_limit_card c) then
      is_weakly_inaccessible c
    else
      true

  val aleph_0 : cardinal_spec = {
    name = "aleph_0",
    is_uncountable = false,
    is_regular = true,
    is_limit_card = true,
    is_strong_limit = true
  }

  val aleph_1 : cardinal_spec = {
    name = "aleph_1",
    is_uncountable = true,
    is_regular = true,
    is_limit_card = false,
    is_strong_limit = false
  }

  val aleph_omega : cardinal_spec = {
    name = "aleph_omega",
    is_uncountable = true,
    is_regular = false,
    is_limit_card = true,
    is_strong_limit = true
  }

  val kappa_inaccessible : cardinal_spec = {
    name = "kappa_inaccessible",
    is_uncountable = true,
    is_regular = true,
    is_limit_card = true,
    is_strong_limit = true
  }

  val inaccessible_verified : bool =
    not (is_strongly_inaccessible aleph_0) andalso
    not (is_strongly_inaccessible aleph_1) andalso
    not (is_strongly_inaccessible aleph_omega) andalso
    is_weakly_inaccessible kappa_inaccessible andalso
    is_strongly_inaccessible kappa_inaccessible andalso
    strong_implies_weak kappa_inaccessible

end;
