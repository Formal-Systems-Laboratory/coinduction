Require Import list_examples.

Definition append_def := FunDef "append" ["x";"y"]
  (SIf ("x" = 0)
    (SReturn "y")
    {{Decl "p";"p" <- "x"
     ;SWhile ("p"->>"next" <> 0) ("p"<- "p"->>"next")
     ;"p" <<- build_node ("p"->>"val") "y"
     ;SReturn "x" }}).

Inductive append_spec : Spec kcfg :=
  append_claim : forall lx x ly y, heap_fun append_spec nil
  append_def [Int x; Int y]
    (rep_list lx x :* rep_list ly y)
    (fun r => rep_list (lx++ly) r)
 |loop_claim : forall lx x ly y lp p, p <> 0 ->
  heap_loop append_spec append_def 0
  ("x" s|-> KInt x :* "y" s|-> KInt y :* "p" s|-> KInt p)
    (rep_seg lx p x :* rep_list lp p :* rep_list ly y)
    (rep_list (lx++lp++ly)).

Lemma append_proof : sound kstep append_spec.
Proof. list_solver.
rewrite app_ass in * |- *.
list_run. Qed.