Require Import trees.

Set Implicit Arguments.

(* Deallocate one tree *)
Definition dealloc_def := FunDef "deallocate" ["t"]
  (SIf ("t"=0)
    SReturnVoid
   {{SCall "deallocate" ["t"->>"left"]
    ;SCall "deallocate" ["t"->>"right"]
    ;HDealloc "t"
    ;SReturnVoid
    }}).
(* Deallocate a whole list of trees *)
Definition iter_dealloc_def := FunDef "iter_deallocate" ["l"]
  {{Decl "lt";
    SWhile ("l" <> 0)
     {{SCall "deallocate" ["l"->>"val"]
      ;"lt" <- "l"
      ;"l" <- "l"->>"next"
      ;HDealloc "lt"
      }};
    SReturnVoid}}.

Inductive dealloc_spec : Spec kcfg :=
  dealloc_claim : forall t p, heap_void_fun dealloc_spec nil
  dealloc_def [Int p] (rep_tree t p) emptyP
 |iter_dealloc_claim : forall l p, heap_void_fun dealloc_spec [dealloc_def]
  iter_dealloc_def [Int p] (rep_prop_list rep_tree l p) (emptyP)
 |iter_dealloc_loop_claim : forall v l p, heap_void_loop dealloc_spec [dealloc_def]
  iter_dealloc_def 0 ("l" s|-> KInt p :* "lt" s|-> v)
  (rep_prop_list rep_tree l p) (emptyP).

Lemma dealloc_proof : sound kstep dealloc_spec.
Proof. tree_solver. Qed.
