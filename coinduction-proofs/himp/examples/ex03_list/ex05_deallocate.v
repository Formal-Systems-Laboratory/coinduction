Require Import list_examples.

Definition dealloc_def := FunDef "dealloc" ["x"]
 {{Decl "y"
  ;SWhile ("x" <> 0)
    {{"y"<-arr_next "x";HDealloc "x";"x"<-"y"}}
  ;SReturn 0}}.

Inductive dealloc_spec : Spec kcfg :=
  dealloc_claim : forall l x, heap_fun dealloc_spec nil
  dealloc_def [Int x] (rep_list l x) (fun r => emptyP)
 |loop_claim  : forall l xv yv, heap_loop dealloc_spec
  dealloc_def 0 ("x" s|-> KInt xv :* "y" s|-> yv)
    (rep_list l xv) (fun r => emptyP).

Lemma dealloc_proof : sound kstep dealloc_spec.
Proof. list_solver. Qed.