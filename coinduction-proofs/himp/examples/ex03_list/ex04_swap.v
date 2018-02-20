Require Import list_examples.

Definition swap_def := FunDef "swap" ["x"]
 {{Decl "p"; "p" <- "x"
  ;"x" <- arr_next "x"
  ;"p"<<-build_node (arr_val "p") (arr_next "x")
  ;"x"<<-build_node (arr_val "x") "p"
  ;SReturn "x"}}.

Inductive swap_spec : Spec kcfg :=
  swap_claim : forall a b l xv, heap_fun swap_spec nil
  swap_def [Int xv]
    (rep_list (a::b::l) xv)
    (rep_list (b::a::l)).

Lemma swap_proof : sound kstep swap_spec.
Proof. list_solver. Qed.