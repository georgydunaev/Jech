Section quot.
Context (A:Type).
Context (R:A->A->Prop).
Context (R_r:forall a1, R a1 a1).
Context (R_s:forall a1 a2, R a1 a2 -> R a2 a1).
Context (R_t:forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3).



