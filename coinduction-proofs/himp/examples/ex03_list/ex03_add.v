Require Import list_examples.

Definition add_fun := FunDef "add" ["v";"x"]
 {{Decl "y";"y"<-EAlloc
  ;"y"<<-build_node "v" "x"
  ;SReturn "y"}}.

Inductive add_spec : Spec kcfg :=
  add_claim : forall v H x l, heap_fun add_spec nil
  add_fun [Int v;Int x]
    (asP H (rep_list l x))
    (fun r => rep_seg (v::nil) x r :* litP H).

Lemma add_proof : sound kstep add_spec.
Proof. list_solver. Qed.