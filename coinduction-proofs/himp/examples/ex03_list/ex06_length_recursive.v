Require Import list_examples.

Definition length_def := FunDef "length" ["x"]
 (SIf ("x" = 0)
   (SReturn 0)
   (SReturn (1 + ECall "length" [arr_next "x"]))).

Inductive length_spec : Spec kcfg :=
  length_claim : forall H l x, heap_fun length_spec nil
  length_def [Int x]
    (asP H (rep_list l x))
    (fun r => constraint (r = zlength l) :* litP H).

Lemma length_proof : sound kstep length_spec.
Proof. list_solver. Qed.