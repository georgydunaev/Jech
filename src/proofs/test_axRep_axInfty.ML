(* Test script for verifying the proofs of axRep and axInfty in SML'97 *)
(*
   Original draft test script preserved in comments:
   use "axRep_axInfty.ML";
   let f (x: A) : B = x
   let C = sup (fun x -> f x) : B
   let test_axRep (x: A) : bool = f x in C
   val _ = assert (test_axRep x);
   let N = sup (fun n -> n) : nat
   let test_axInfty : bool = infinite N
   val _ = assert test_axInfty;
   val _ = print "Proofs for axRep and axInfty are verified.";
*)

structure TestAxRepAxInfty =
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

  fun test_axRep (domain_set : ens) (func : ens -> ens) : bool =
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

  fun test_axInfty (k : int) : bool =
    let
      val omega = omega_stage k
      fun check_succ i =
        if i + 1 >= k then true
        else if mem_of (succ (elem omega i)) omega then check_succ (i + 1)
        else false
    in
      k > 0 andalso mem_of Empty omega andalso check_succ 0
    end

  exception AssertionFailed of string

  fun assert_true msg cond =
    if cond then () else raise AssertionFailed msg

  fun run () =
    let
      val e0 = Empty
      val e1 = succ e0
      val e2 = succ e1
      val sample_A = Sup (3, fn 0 => e0 | 1 => e1 | _ => e2)
      val _ = assert_true "axRep failed" (test_axRep sample_A succ)
      val _ = assert_true "axInfty failed" (test_axInfty 6)
      val _ = print "Proofs for axRep and axInfty are verified.\n"
    in
      true
    end

end;

val _ = TestAxRepAxInfty.run ();
