Require Import list_examples.

Definition head_def := FunDef "head" ["x"]
  (SReturn ("x"->>"val")).

Inductive head_spec : Spec kcfg :=
  head_claim : forall p H x l, heap_fun head_spec nil
  head_def [Int p]
    (asP H (rep_list (x::l) p))
    (fun r => constraint (r=x) :* litP H).

Lemma head_proof : sound kstep head_spec.
Proof. list_solver. Qed.