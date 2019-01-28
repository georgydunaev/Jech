(*
  forall R:forall x:A, B x -> Prop,
    (forall x:A, exists y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).
*)

Section sec_DC.
Context (DC: DependentFunctionalChoice).
Context (S:Ens).
Context (H:~IN Vide S).
Definition A:Type:=pi1 S.
Check (DC A).
Context (z:A) (X:Ens) (G:IN X S).
Definition oldB:=pi1 (Union S).
Check (@sig (oldB) (fun t:oldB=>EQ X (pi2 (Union S) t))).
Definition L (Z:Ens):={t : oldB | EQ Z (pi2 (Union S) t)}.


Definition P:= fun (ts:pi1 S)
(tus: L (pi2 S ts) ) => IN (pi2 (Union S) tus) (pi2 S ts).


Definition B : A -> Type := fun z:A => pi1 ().

pi1 (Union S).




Theorem hyp : forall a : A, (exists b : B, P a b).

Theorem thm0: True.
unfold DependentFunctionalChoice in DC.
pose (DC
 

End sec_DC.