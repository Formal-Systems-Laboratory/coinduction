Require Import list_examples.

Definition rev_app_body :=
  (If (Var 0)
    (Let (Deref (Var 0)) (Lam
      (Seq (Assign (Var 1) (Cons (Car (Var 0)) (Var 2)))
           ((Var 3) (Var 1) (Cdr (Var 0))))))
    (Var 1)).
Definition list_rev_app :=
  strict_fix (Lam (Lam (Lam rev_app_body))).
Definition list_rev_body := list_rev_app Nil (Var 0).
Definition list_rev := Lam list_rev_body.

Inductive reverse_spec : Spec cfg :=
  rev_claim : forall l pl env, exp_val reverse_spec
  list_rev_body (pl::env)
    (rep_list l pl)
    (rep_list (rev l))
 |rev_app_claim : forall k l pk pl env, exp_val reverse_spec
  rev_app_body (pl::pk::fix_env (Lam (Lam rev_app_body)) env)
    (rep_list k pk :* rep_list l pl)
    (rep_list (rev_append l k)).

Lemma reverse_proof : sound lam_step reverse_spec.
Proof. list_solver;
rewrite <- rev_alt in * |- ;
list_run. Qed.