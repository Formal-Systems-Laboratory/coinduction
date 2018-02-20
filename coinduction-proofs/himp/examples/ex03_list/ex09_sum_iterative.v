Require Import list_examples.

Definition sum_def := FunDef "sum" ["x"]
 {{Decl "s";"s"<-0
  ;SWhile ("x"<>0) {{"s"<-"s"+arr_val "x"; "x"<-arr_next "x"}}
  ;SReturn "s"}}.

Inductive sum_spec : Spec kcfg :=
  sum_claim : forall H l x, heap_fun sum_spec nil
  sum_def [Int x]
    (asP H (rep_list l x))
    (fun r => constraint (r = sum l) :* litP H)
 |loop_claim : forall k H l x, heap_loop sum_spec
  sum_def 0 ("s" s|-> KInt k :* "x" s|-> KInt x)
    (asP H (rep_list l x))
    (fun r => constraint (r = k + sum l) :* litP H).

Lemma sum_proof : sound kstep sum_spec.
Proof. list_solver. Qed.
