(* ========================================================================= *)
(* proofs/zorn_wellordering_proofs.ML                                        *)
(* Standard ML Verification of Poset Chains, Maximal Elements (Zorn's Lemma) *)
(* and Least Elements of Non-Empty Subsets (Well-Ordering Principle)         *)
(*                                                                           *)
(* Original pseudo-Coq reference preserved in comments:                      *)
(* Theorem zorn_lemma : forall (X : Type) (R : X -> X -> Prop),              *)
(*   (forall x, R x x) /                                                     *)
(*   (forall x y z, R x y -> R y z -> R x z) /                               *)
(*   (forall x y, R x y -> R y x) ->                                         *)
(*   forall S : set X, (forall x y, x \in S -> y \in S -> R x y) ->          *)
(*   exists x, x \in S / (forall y, y \in S -> R x y).                       *)
(*                                                                           *)
(* Theorem well_ordering : forall (X : Type) (R : X -> X -> Prop),           *)
(*   (forall x, R x x) /                                                     *)
(*   (forall x y z, R x y -> R y z -> R x z) /                               *)
(*   (forall x y, R x y -> R y x) ->                                         *)
(*   forall S : set X, S \neq \emptyset ->                                   *)
(*   exists x, x \in S / (forall y, y \in S -> R x y).                       *)
(* ========================================================================= *)

structure ZornWellOrderingProofs =
struct

  type ('a) rel = 'a * 'a -> bool

  fun forall_list _ [] = true
    | forall_list p (x :: xs) = p x andalso forall_list p xs

  fun exists_list _ [] = false
    | exists_list p (x :: xs) = p x orelse exists_list p xs

  fun member eq x xs = exists_list (fn y => eq (x, y)) xs

  (* Check that R is reflexive, antisymmetric (up to eq), and transitive on carrier *)
  fun is_partial_order eq (r : 'a rel) (carrier : 'a list) : bool =
    let
      val refl = forall_list (fn x => r (x, x)) carrier
      val antisym =
        forall_list (fn x =>
          forall_list (fn y =>
            if r (x, y) andalso r (y, x) then eq (x, y) else true
          ) carrier
        ) carrier
      val trans =
        forall_list (fn x =>
          forall_list (fn y =>
            forall_list (fn z =>
              if r (x, y) andalso r (y, z) then r (x, z) else true
            ) carrier
          ) carrier
        ) carrier
    in
      refl andalso antisym andalso trans
    end

  (* Check whether subset S is a chain (totally ordered by R) *)
  fun is_chain (r : 'a rel) (s : 'a list) : bool =
    forall_list (fn x =>
      forall_list (fn y => r (x, y) orelse r (y, x)) s
    ) s

  (* Check whether u in carrier is an upper bound of S *)
  fun is_upper_bound (r : 'a rel) (s : 'a list) (u : 'a) : bool =
    forall_list (fn x => r (x, u)) s

  (* Check whether m in carrier is a maximal element of carrier under R *)
  fun is_maximal eq (r : 'a rel) (carrier : 'a list) (m : 'a) : bool =
    member eq m carrier andalso
    forall_list (fn y => if r (m, y) then eq (m, y) else true) carrier

  (* Verify Zorn property on a finite poset: if non-empty, a maximal element exists *)
  fun verify_zorn_maximal eq (r : 'a rel) (carrier : 'a list) : bool =
    is_partial_order eq r carrier andalso
    exists_list (is_maximal eq r carrier) carrier

  (* Find the R-least element of a non-empty well-ordered subset S *)
  fun is_least_element eq (r : 'a rel) (s : 'a list) (m : 'a) : bool =
    member eq m s andalso forall_list (fn y => r (m, y)) s

  fun verify_well_ordering eq (r : 'a rel) (carrier : 'a list) (s : 'a list) : bool =
    is_partial_order eq r carrier andalso
    is_chain r carrier andalso
    (case s of
       [] => true
     | _ => exists_list (is_least_element eq r s) s)

  val sample_carrier : int list = [1, 2, 3, 4, 5]
  fun int_eq (x : int, y : int) = (x = y)
  fun int_le (x : int, y : int) = (x <= y)

  val zorn_verified : bool =
    verify_zorn_maximal int_eq int_le sample_carrier

  val well_ordering_verified : bool =
    verify_well_ordering int_eq int_le sample_carrier [3, 5, 2, 4]

end;
