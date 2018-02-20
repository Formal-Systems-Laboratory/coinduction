Require Import list_examples.

Definition dealloc_body :=
 (If (Var 0) (Let (Deref (Var 0)) (Lam
   (Seq (Dealloc (Var 1))
        ((Var 2) (Cdr (Var 0))))))
   Nil).

Inductive dealloc_spec : Spec cfg :=
  dealloc_claim : forall l r env, exp_val dealloc_spec
  dealloc_body (r::fix_env (Lam dealloc_body) env)
    (rep_list l r) (fun v => constraint (v = Nil)).

Lemma dealloc_proof : sound lam_step dealloc_spec.
Proof. list_solver. Qed.