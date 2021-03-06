Require Import trees.

Definition tree_to_list_loop :=
  SWhile ("s" <> 0)
  {{"sn" <- "s"
   ;"tn"<- "sn"->>"val"
   ;"s" <- "s"->>"next"
   ;HDealloc "sn"
   ;SIf ("tn"->>"left" <> 0)
     {{"sn" <- EAlloc
      ;"sn"<<- build_node ("tn"->>"left") "s"
      ;"s"  <- "sn"
      }} Skip
   ;SIf ("tn"->>"right"<>0)
     {{"sn"<- EAlloc;"sn"<<- build_node "tn" "s";"s"  <- "sn"
      ;"sn"<- EAlloc;"sn"<<- build_node ("tn"->>"right") "s";"s" <- "sn"
      ;"tn"<<- build_tree ("tn"->>"val") 0 0
      }}
     {{"ln" <- EAlloc;"ln"<<- build_node ("tn"->>"val") "l";"l"<-"ln"
      ;HDealloc "tn"}}
   }}.
Definition tree_to_list_def := FunDef "tree_to_list" ["t"]
 {{SIf ("t"=0) (SReturn 0) Skip
  (* Start the list *)
  ;Decl "l";"l" <- 0
  (* An explicit stack of trees we are processing *)
  ;Decl "s";"s" <- EAlloc; "s" <<- build_node "t" 0
  ;Decl "sn";Decl "tn";Decl "ln"
  ;tree_to_list_loop
  ;SReturn "l"}}.

Fixpoint tree2List t :=
  match t with
    | Leaf => nil
    | Node v l r => tree2List l ++ v :: tree2List r
  end.
Fixpoint trees2List ts :=
  match ts with
    | nil => nil
    | t :: ts => tree2List t ++ trees2List ts
  end.
Inductive tree_to_list_spec : Spec kcfg :=
  loop_claim : forall ts t l s tn lv ln sn, heap_loop tree_to_list_spec
    tree_to_list_def 0 ("t" s|-> KInt t :* "l" s|-> KInt l :* "s" s|-> KInt s
                :* "tn" s|-> tn :* "ln" s|-> ln :* "sn" s|-> sn)
    (rep_prop_list (fun t p => constraint (p <> 0) :* rep_tree t p) ts s :* rep_list lv l)
    (rep_list (trees2List (rev ts) ++ lv))
| tree_to_list_claim : forall t p, heap_fun tree_to_list_spec nil
    tree_to_list_def [Int p] (rep_tree t p) (rep_list (tree2List t)).

Lemma trees2List_app : forall l1 l2, trees2List (l1 ++ l2) = trees2List l1 ++ trees2List l2.
Proof. induction l1;intros;[|simpl;rewrite IHl1, app_ass];reflexivity. Qed.
Hint Rewrite trees2List_app : trans_simpl.

Lemma tree_to_list_proof : sound kstep tree_to_list_spec.
Proof. tree_solver;
simpl in * |- *;simplify_pat_hyps;subst;tree_run.
Qed.
