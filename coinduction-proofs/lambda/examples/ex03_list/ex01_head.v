Require Import list_examples.

Definition head_body := Car (Deref (Var 0)).

Inductive head_spec : Spec cfg :=
  head_claim : forall H x l r env, exp_val head_spec
  head_body (Addr r::env)
    (asP H (rep_list (x::l) (Addr r)))
    (fun v => constraint (v = x) :* litP H).

Lemma heap_proof : sound lam_step head_spec.
Proof. list_solver. Qed.