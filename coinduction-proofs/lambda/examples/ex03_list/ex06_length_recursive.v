Require Import list_examples.

Definition length_body :=
  If (Var 0) (Inc ((Var 1) (Cdr (Deref (Var 0))))) (Num 0).

Inductive length_spec : Spec cfg :=
  length_claim : forall H l r env, exp_val length_spec
  length_body (r::fix_env (Lam length_body) env)
    (asP H (rep_list l r))
    (fun v => constraint (v = Num (length l)) :* litP H).

Lemma length_proof : sound lam_step length_spec.
Proof. list_solver. Qed.