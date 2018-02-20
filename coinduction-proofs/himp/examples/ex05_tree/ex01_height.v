Require Import ZArith.
Require Import String.
Require Import trees.

Set Implicit Arguments.

Definition maxDef := FunDef "max" ["x";"y"]
  (SIf (BLe (EVar "x") (EVar "y")) (SReturn (EVar "y")) (SReturn (EVar "x"))).

Definition heightDef := FunDef "tree_height" ["t"]
  (SIf ("t" = 0)
      (SReturn 0)
      (SReturn (1 + ECall "max"
                      [ECall "tree_height" ["t"->>"left"]
                      ;ECall "tree_height" ["t"->>"right"]
                      ])))%code.

Inductive height_spec : Spec kcfg :=
  height_claim : forall H t p, heap_fun height_spec [maxDef]
  heightDef [Int p] (asP H (rep_tree t p))
  (fun r => constraint (r = height t) :* litP H)%pattern.

Lemma height_proof : sound kstep height_spec.
tree_solver.
(* Need to rewrite by Zmax_right / Zmax_left to finish. *)
rewrite Zmax_right by auto with zarith; tree_run.
rewrite Zmax_left by auto with zarith; tree_run.
Qed.