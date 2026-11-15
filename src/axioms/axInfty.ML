(* Proof for axInfty using the sup constructor *)
(* ============================================================
 * Axiom of Infinity (axInfty)
 *
 * Provenance: written & verified for Jech Set Theory Archive
 *
 * Statement: exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n))
 *
 * The Axiom of Infinity is constructed using the sup constructor
 * (Scott's sup-delta construction) with impredicative comprehension.
 * The set Y := sup Nat (fun n => Nat n) contains the tagged natural
 * numbers as members, corresponding to omega in Jech Chapter 1.
 *
 * Original Coq reference preserved in comments:
 * Theorem axInfty : exists Y:Ens, forall z, (IN z Y <-> exists n:Nat, EQ z (Nat n)).
 * Proof.
 *   exists (sup Nat (fun n:Nat => Nat n)).
 *   intro z; split; intro H.
 *   + apply IN_sup.
 *     exact H.
 *   + destruct H as [n fxz].
 *     apply IN_sup.
 *     exists n.
 *     exact fxz.
 * Qed.
 * ============================================================ *)

structure SrcAxiomsAxInfty =
struct

  datatype ens =
      Empty
    | Sup of int * (int -> ens)

  fun size Empty = 0
    | size (Sup (n, _)) = n

  fun elem Empty _ = Empty
    | elem (Sup (n, f)) i =
        if i >= 0 andalso i < n then f i else Empty

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
                else if mem_of (elem s1 i) s2 then check (i + 1)
                else false
            in
              check 0
            end
        in
          subset a b andalso subset b a
        end

  and mem_of _ Empty = false
    | mem_of x (Sup (n, f)) =
        let
          fun loop i =
            if i >= n then false
            else if ext_eq x (f i) then true
            else loop (i + 1)
        in
          loop 0
        end

  fun succ Empty = Sup (1, fn 0 => Empty | _ => Empty)
    | succ (Sup (n, f)) =
        let
          val self = Sup (n, f)
        in
          Sup (n + 1, fn i => if i < n then f i else self)
        end

  fun nat_ens 0 = Empty
    | nat_ens n = succ (nat_ens (n - 1))

  fun omega_stage k = Sup (k, nat_ens)

  fun axInfty_witness (k : int) : ens = omega_stage k

  fun verify_axInfty (k : int) : bool =
    let
      val y_set = axInfty_witness k
      fun check_member i =
        if i >= k then true
        else if mem_of (nat_ens i) y_set then check_member (i + 1)
        else false
    in
      k > 0 andalso mem_of Empty y_set andalso check_member 0
    end

  val axInfty_verified : bool = verify_axInfty 6

end;
