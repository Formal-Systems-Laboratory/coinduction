Require Import trees.

Set Implicit Arguments.

Definition mirrorDef := FunDef "mirror" ["t"]
  (SIf ("t" = 0)
      SReturnVoid
     {{"t" <<- build_tree ("t"->>"val") ("t"->>"right") ("t"->> "left")
      ;SCall "mirror" ["t"->>"left"]
      ;SCall "mirror" ["t"->>"right"]
      ;SReturnVoid
      }}).

Fixpoint mirror t := match t with
    | Leaf => Leaf
    | Node v l r => Node v (mirror r) (mirror l)
  end.
Inductive mirror_spec : Spec kcfg :=
  height_claim : forall t p, heap_void_fun mirror_spec nil
  mirrorDef [Int p] (rep_tree t p) (rep_tree (mirror t) p).

Lemma mirror_proof : sound kstep mirror_spec.
Proof. tree_solver. Qed.
