Require Import list_examples.

Definition tail_def := FunDef "tail" ["x"]
  (SReturn ("x"->>"next")).

Inductive tail_spec : Spec kcfg :=
  tail_claim : forall H p x y l, heap_fun tail_spec nil
  tail_def [Int p]
    (asP H (rep_seg (x::nil) y p :* rep_list l y))
    (fun r => constraint (r = y) :* litP H).

Lemma tail_proof : sound kstep tail_spec.
Proof. list_solver. Qed.