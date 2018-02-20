Require Import list_examples.

Definition tail_body := Cdr (Deref (Var 0)).

Inductive tail_spec : Spec cfg :=
  tail_claim : forall H r y x l env, exp_val tail_spec
  tail_body (Addr r::env)
    (asP H (rep_list l y :* list_seg (x::nil) y (Addr r)))
    (fun v => constraint (v = y) :* litP H).

Lemma tail_proof : sound lam_step tail_spec.
Proof. list_solver. Qed.
