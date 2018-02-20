Require Import list_examples.

Definition swap_body :=
   Let (Deref (Var 0)) (Lam
  (Seq (Assign (Var 1) (Cons (Car (Deref (Cdr (Var 0))))
                             (Cdr (Var 0))))
  (Seq (Assign (Cdr (Var 0)) (Cons (Car (Var 0))
                                   (Cdr (Deref (Cdr (Var 0))))))
       (Var 1)))).

Inductive swap_spec : Spec cfg :=
  swap_claim : forall x y l r env, exp_val swap_spec
  swap_body (r::env)
    (rep_list (x::y::l) r)
    (rep_list (y::x::l)).
                 
Lemma swap_proof : sound lam_step swap_spec.
Proof. list_solver. Qed.
