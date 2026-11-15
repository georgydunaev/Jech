(* Proof for axRep using the sup constructor *)
(* ============================================================
 * Axiom of Replacement (axRep)
 *
 * Statement: The Axiom of Replacement states that if for every element
 * x in a set A there is a unique element y such that a functional
 * relation R(x, y) holds, then there exists a set C = { F(x) : x in A }
 * containing the image of A under F.
 *
 * Original pseudo-code preserved in comments:
 * let f (x: A) : B = x
 * let C = sup (fun x -> f x) : B
 * let axRep_proof (x: A) : f x in C = true
 * let N = sup (fun n -> n) : nat
 * let axInfty_proof : infinite N = true
 * ============================================================ *)

structure SrcAxiomsAxRep =
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

  fun verify_axRep (domain_set : ens) (func : ens -> ens) : bool =
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

  val sample_domain : ens =
    let
      val e0 = Empty
      val e1 = succ e0
      val e2 = succ e1
    in
      Sup (3, fn 0 => e0 | 1 => e1 | _ => e2)
    end

  val axRep_verified : bool = verify_axRep sample_domain succ

end;
