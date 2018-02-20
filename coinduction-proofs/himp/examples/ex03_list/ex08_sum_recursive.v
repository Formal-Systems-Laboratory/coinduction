Require Import list_examples.

Definition sum_def := FunDef "sum_recursive" ["x"]
 (SIf ("x"=0)
   (SReturn 0)
   (SReturn (arr_val "x"
           + ECall "sum_recursive" [arr_next "x"]))).

Inductive sum_spec : Spec kcfg :=
  sum_claim : forall H l x, heap_fun sum_spec nil
  sum_def [Int x]
    (asP H (rep_list l x))
    (fun r => constraint (r = sum l) :* litP H).

Lemma sum_proof : sound kstep sum_spec.
Proof. list_solver. Qed.
