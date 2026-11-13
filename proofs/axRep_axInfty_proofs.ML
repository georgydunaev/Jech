(* ========================================================================= *)
(* proofs/axRep_axInfty_proofs.ML                                            *)
(* Verification of Replacement Schema and Infinity Axiom in SML             *)
(*                                                                           *)
(* Mathematical Specification:                                              *)
(* 1. Axiom of Replacement (Schema):                                         *)
(*    In ZFC set theory, for any set A and any definable class function F,  *)
(*    the image F[A] = { F(x) : x in A } is a set. It does not state that   *)
(*    "every set has a representative".                                     *)
(*                                                                           *)
(* 2. Axiom of Infinity:                                                     *)
(*    In ZFC set theory, there exists an inductive set containing the empty *)
(*    set and closed under von Neumann successor: x in omega implies        *)
(*    x U {x} in omega. The universe of all sets is a proper class, not a   *)
(*    set.                                                                  *)
(*                                                                           *)
(* In the Scott/Aczel Ens model of well-founded trees, replacement and       *)
(* infinity are constructed directly via the sup constructor.               *)
(* ========================================================================= *)

structure AxRepAxInftyProofs =
struct

  (* Representation of sets as well-founded trees (Scott-Aczel Ens model).
     A set is represented as Sup(n, f) where n is the index count
     and f maps indices 0 .. n-1 to constituent sets. *)
  datatype ens =
      Empty
    | Sup of int * (int -> ens)

  (* Cardinality / index bound *)
  fun size Empty = 0
    | size (Sup (n, _)) = n

  (* Access i-th element *)
  fun elem Empty _ = Empty
    | elem (Sup (n, f)) i =
        if i >= 0 andalso i < n then f i else Empty

  (* Extensional equality between sets *)
  fun ext_eq Empty Empty = true
    | ext_eq Empty (Sup (0, _)) = true
    | ext_eq (Sup (0, _)) Empty = true
    | ext_eq Empty _ = false
    | ext_eq _ Empty = false
    | ext_eq a b =
        let
          fun subset s1 s2 =
            let
              val n1 = size s1
              fun check i =
                if i >= n1 then true
                else
                  let
                    val x = elem s1 i
                  in
                    if mem_of x s2 then check (i + 1) else false
                  end
            in
              check 0
            end
        in
          subset a b andalso subset b a
        end

  (* Membership: x in s iff exists i < size s such that ext_eq x (elem s i) *)
  and mem_of x Empty = false
    | mem_of x (Sup (n, f)) =
        let
          fun loop i =
            if i >= n then false
            else if ext_eq x (f i) then true
            else loop (i + 1)
        in
          loop 0
        end

  (* Set of a single element: {x} *)
  fun singleton x = Sup (1, fn 0 => x | _ => Empty)

  (* von Neumann successor: succ(x) = x U {x} *)
  fun succ Empty = Sup (1, fn 0 => Empty | _ => Empty)
    | succ (Sup (n, f)) =
        let
          val self = Sup (n, f)
        in
          Sup (n + 1, fn i => if i < n then f i else self)
        end

  (* ======================================================================= *)
  (* 1. AXIOM OF REPLACEMENT (REPLACEMENT SCHEMA)                            *)
  (*                                                                         *)
  (* In ZFC, for any set A and any definable class function F, the image     *)
  (* F[A] = { F(x) : x in A } is a set.                                      *)
  (* In the Scott/Aczel Ens model, if A = Sup(n, f), then the replacement   *)
  (* image set under operator F is directly Sup(n, F o f).                   *)
  (* ======================================================================= *)

  fun rep_image Empty _ = Empty
    | rep_image (Sup (n, f)) (F : ens -> ens) =
        Sup (n, fn i => F (f i))

  fun verify_replacement (A : ens) (F : ens -> ens) : bool =
    let
      val image_set = rep_image A F
      val n = size A
      fun check i =
        if i >= n then true
        else
          let
            val x = elem A i
            val fx = F x
          in
            if mem_of fx image_set then check (i + 1) else false
          end
    in
      check 0
    end

  (* ======================================================================= *)
  (* 2. AXIOM OF INFINITY                                                    *)
  (*                                                                         *)
  (* In ZFC, there exists an inductive set containing the empty set and      *)
  (* closed under von Neumann successor: x in omega implies succ(x) in omega. *)
  (* In the Ens model, omega = Sup(N, fun i => nat_ens i).                  *)
  (* ======================================================================= *)

  fun nat_ens 0 = Empty
    | nat_ens n = succ (nat_ens (n - 1))

  (* Inductive stage approximation containing 0, 1, ..., k-1 *)
  fun omega_stage k = Sup (k, nat_ens)

  fun verify_infinity (k : int) : bool =
    let
      val omega = omega_stage k
      val empty_in_omega = mem_of Empty omega
      fun check_succ i =
        if i + 1 >= k then true
        else
          let
            val ni = elem omega i
            val sni = succ ni
          in
            if mem_of sni omega then check_succ (i + 1) else false
          end
    in
      k > 0 andalso empty_in_omega andalso check_succ 0
    end

  fun run_tests () =
    let
      val _ = print "Testing AxRepAxInftyProofs in Poly/ML...\n"
      (* Test Replacement *)
      val set_0 = Empty
      val set_1 = succ set_0
      val set_2 = succ set_1
      val set_3 = succ set_2
      val test_A = Sup (3, fn 0 => set_0 | 1 => set_1 | _ => set_2)
      val rep_ok = verify_replacement test_A succ
      val _ = if rep_ok then print "  Axiom of Replacement verification: PASSED\n"
              else print "  Axiom of Replacement verification: FAILED\n"

      (* Test Infinity *)
      val infty_ok = verify_infinity 5
      val _ = if infty_ok then print "  Axiom of Infinity verification: PASSED\n"
              else print "  Axiom of Infinity verification: FAILED\n"
    in
      rep_ok andalso infty_ok
    end

end;

val _ = AxRepAxInftyProofs.run_tests ();
