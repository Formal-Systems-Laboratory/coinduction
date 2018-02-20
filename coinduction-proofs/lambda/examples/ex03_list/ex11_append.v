Require Import list_examples.

Definition list_app_nonempty_body :=
 Let (Deref (Var 0)) (Lam
 (If (Cdr (Var 0))
     ((Var 2) (Cdr (Var 0)))
     (Assign (Var 1) (Cons (Car (Var 0)) (Var 3))))).
Definition list_app_nonempty :=
  strict_fix (Lam (Lam list_app_nonempty_body)).
Definition list_app_body :=
  If (Var 1) (Seq (list_app_nonempty (Var 1)) (Var 1)) (Var 0).
Definition list_app := Lam (Lam list_app_body).

Inductive append_spec : Spec cfg :=
  append_claim : forall lx ly px py env, exp_val append_spec
  list_app_body (py::px::env)
    (rep_list lx px :* rep_list ly py)
    (rep_list (lx++ly))
 |append_nonempty_claim : forall x lx px p ly py env,
  exp_val append_spec list_app_nonempty_body
      (Addr p::fix_env (Lam list_app_nonempty_body) (py::env))
    (p |-> Pair x px :* rep_list lx px :* rep_list ly py)
    (fun _ => rep_list(x::lx++ly) (Addr p)).
    
Lemma append_proof : sound lam_step append_spec.
Proof. list_solver. Qed.