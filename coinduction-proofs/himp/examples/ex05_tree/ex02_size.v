Require Import trees.

Definition sizeDef := FunDef "size" ["t"]
 (SIf ("t" = 0)
      (SReturn 0)
      (SReturn (1 + ECall "size" ["t"->>"left"]
                  + ECall "size" ["t"->>"right"])))%code.

Inductive size_spec : Spec kcfg :=
  size_claim : forall H t p, heap_fun size_spec nil
  sizeDef [Int p] (asP H (rep_tree t p))
  (fun r => constraint (r = size t) :* litP H)%pattern.

Lemma size_proof : sound kstep size_spec.
Proof. tree_solver. Qed.