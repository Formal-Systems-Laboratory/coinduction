Require Import list_examples.

Definition copy_body :=
  (If (Var 0) (Let (Deref (Var 0)) (Lam
    (Ref (Cons (Car (Var 0)) ((Var 2) (Cdr (Var 0)))))))
  Nil).

Inductive copy_spec : Spec cfg :=
  copy_claim : forall H l pl env, exp_val copy_spec
  copy_body (pl::fix_env (Lam copy_body) env)
    (asP H (rep_list l pl))
    (fun r => rep_list l r :* litP H).

Lemma copy_proof : sound lam_step copy_spec.
Proof. list_solver. Qed.