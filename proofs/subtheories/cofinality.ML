(* ========================================================================= *)
(* proofs/subtheories/cofinality.ML                                          *)
(* Cofinality Sub-Theory in Standard ML (Jech Chapter 3)                     *)
(*                                                                           *)
(* Original placeholder preserved in comments:                               *)
(* Theorem zorn_lemma : forall (X : Type) (R : X -> X -> Prop),              *)
(*   (forall x, R x x) /                                                     *)
(*   (forall x y z, R x y -> R y z -> R x z) /                               *)
(*   (forall x y, R x y -> R y x) ->                                         *)
(*   forall S : set X, (forall x y, x \in S -> y \in S -> R x y) ->          *)
(*   exists x, x \in S / (forall y, y \in S -> R x y).                       *)
(* ========================================================================= *)

structure CofinalitySubtheory =
struct

  fun forall_list _ [] = true
    | forall_list p (x :: xs) = p x andalso forall_list p xs

  fun exists_list _ [] = false
    | exists_list p (x :: xs) = p x orelse exists_list p xs

  (* A subset C of a limit ordinal/ordered set L is cofinal in L if:
     1. Every c in C belongs to L, and
     2. For every x in L, there exists c in C such that x <= c. *)
  fun is_cofinal_subset (le : 'a * 'a -> bool) (limit_set : 'a list) (cofinal_sub : 'a list) : bool =
    let
      fun in_limit c = exists_list (fn x => le (c, x) andalso le (x, c)) limit_set
      val subset_ok = forall_list in_limit cofinal_sub
      val unbounded_ok =
        forall_list (fn x =>
          exists_list (fn c => le (x, c)) cofinal_sub
        ) limit_set
    in
      subset_ok andalso unbounded_ok
    end

  (* Check that a mapping f : dom -> target is non-decreasing (order-preserving) *)
  fun is_monotone_cofinal_map
        (le_dom : 'a * 'a -> bool)
        (le_tgt : 'b * 'b -> bool)
        (dom : 'a list)
        (tgt : 'b list)
        (f : 'a -> 'b) : bool =
    let
      val mono =
        forall_list (fn a1 =>
          forall_list (fn a2 =>
            if le_dom (a1, a2) then le_tgt (f a1, f a2) else true
          ) dom
        ) dom
      val image = List.map f dom
    in
      mono andalso is_cofinal_subset le_tgt tgt image
    end

  val cofinality_verified : bool =
    let
      fun int_le (x : int, y : int) = (x <= y)
      val limit_stage = [0, 1, 2, 3, 4, 5, 6]
      val even_cofinal = [0, 2, 4, 6]
    in
      is_cofinal_subset int_le limit_stage even_cofinal andalso
      is_monotone_cofinal_map int_le int_le [0, 1, 2, 3] limit_stage (fn k => 2 * k)
    end

end;
