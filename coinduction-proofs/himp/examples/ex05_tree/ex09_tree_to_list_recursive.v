Require Import trees.

Definition tree_to_list_rec_def := FunDef "tree_to_list_recursive" ["t";"l"]
  (SIf ("t"=0)
       (SReturn "l")
      {{"l" <- ECall "tree_to_list_recursive" ["t"->>"right"; EVar "l"]
       ;Decl "ln"
       ;"ln"<-EAlloc
       ;"ln"<<- build_node ("t"->>"val") "l"
       ;"l"<- ECall "tree_to_list_recursive" ["t"->>"left"; EVar "ln"]
       ;HDealloc "t"
       ;SReturn "l"
       }}).
Definition tree_to_list_def := FunDef "tree_to_list" ["t"]
  (SReturn (ECall "tree_to_list_recursive" [EVar "t";ECon 0])).

Fixpoint tree2List t :=
  match t with
    | Leaf => nil
    | Node v l r => tree2List l ++ v :: tree2List r
  end.

Inductive tree_to_list_spec : Spec kcfg :=
  tree_to_list_claim : forall t p, heap_fun tree_to_list_spec [tree_to_list_rec_def]
  tree_to_list_def [Int p] (rep_tree t p) (rep_list (tree2List t))
 (* <k>tree_to_list(P) => ?R...</k>
    <heap>... tree(T,P) => list(tree2List(T),?R) ...</heap> *)
 |tree_to_list_rec_claim : forall t p l lp, heap_fun tree_to_list_spec nil
  tree_to_list_rec_def [Int p;Int lp] (rep_tree t p :* rep_list l lp)
  (rep_list (tree2List t++l))
 (* <k>tree_to_list_recursive(P,LP) => ?R...</k>
    <heap>... tree(T,P), list(L,LP) => list(tree2List(T)++L,?R) ...</heap> *).

Lemma tree_to_list_proof : sound kstep tree_to_list_spec.
Proof. tree_solver. Qed.