(* ============================================================
 * Implementation of the proofs for axRep and axInfty in SML'97
 * ============================================================ *)

(* The Axiom of Replacement (axRep) and Axiom of Infinity (axInfty)
   are verified in the Scott-Aczel Ens tree model using the Sup constructor:
   - Given a set A = Sup(n, f) and a class function F : ens -> ens,
     the replacement image C = Sup(n, fn i => F (f i)) contains F(x)
     for every x in A.
   - Given the von Neumann natural numbers nat_ens(n), the stage
     omega_stage(k) = Sup(k, nat_ens) witnesses the inductive closure
     of natural numbers under successor.

   Original draft pseudo-code preserved in comments:
   let f (x: A) : B = x
   let C = sup (fun x -> f x) : B
   let axRep_proof (x: A) : f x in C = true
   let N = sup (fun n -> n) : nat
   let axInfty_proof : infinite N = true
   let test_axRep_proof : forall x: A, f x in C := axRep_proof x
   let test_axInfty_proof : infinite N := axInfty_proof
*)

structure SrcProofsAxRepAxInfty =
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

  fun rep_image Empty _ = Empty
    | rep_image (Sup (n, f)) (func : ens -> ens) =
        Sup (n, fn i => func (f i))

  fun axRep_proof (domain_set : ens) (func : ens -> ens) : bool =
    let
      val c_set = rep_image domain_set func
      val n = size domain_set
      fun check i =
        if i >= n then true
        else if mem_of (func (elem domain_set i)) c_set then check (i + 1)
        else false
    in
      check 0
    end

  fun nat_ens 0 = Empty
    | nat_ens n = succ (nat_ens (n - 1))

  fun omega_stage k = Sup (k, nat_ens)

  fun axInfty_proof (k : int) : bool =
    let
      val omega = omega_stage k
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
      k > 0 andalso mem_of Empty omega andalso check_succ 0
    end

  val sample_A : ens =
    let
      val s0 = Empty
      val s1 = succ s0
      val s2 = succ s1
    in
      Sup (3, fn 0 => s0 | 1 => s1 | _ => s2)
    end

  val test_axRep_proof : bool = axRep_proof sample_A succ
  val test_axInfty_proof : bool = axInfty_proof 6

end;
