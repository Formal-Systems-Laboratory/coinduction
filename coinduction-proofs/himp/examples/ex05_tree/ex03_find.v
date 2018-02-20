Require Import trees.

Set Implicit Arguments.

Definition find_code :=
  FunDef "find" ["v"; "t"]
  (SIf ("t"=0)
    (SReturn false)
    (SReturn (("v"="t"->>"val")
             || ECall "find" [EVar "v"; "t"->>"left"]
             || ECall "find" [EVar "v"; "t"->>"right"])))%code.

Fixpoint contains_bool v t :=
  match t with
    | Leaf => false
    | Node v' l r =>
         orb (Z.eqb v v') (orb (contains_bool v l) (contains_bool v r))
  end.
Inductive find_spec : Spec kcfg  :=
  find_claim : forall v H t p, heap_gen_fun find_spec
  find_code [Int v;Int p] (asP H (rep_tree t p))
  (fun r => constraint (r = KBool (contains_bool v t)) :* litP H)%pattern.

Lemma find_proof : sound kstep find_spec.
Proof. tree_solver;destruct (contains_bool v t1) eqn: ?;tree_run. Qed.