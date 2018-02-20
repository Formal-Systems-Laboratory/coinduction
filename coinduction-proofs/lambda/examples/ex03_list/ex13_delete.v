Require Import list_examples.

Definition delete_body :=
  (If (Var 0)
   (Let (Deref (Var 0)) (Lam
   (If (Eq (Var 3) (Car (Var 0)))
       (Seq (Dealloc (Var 1)) ((Var 2) (Cdr (Var 0))))
       (Seq (Assign (Var 1) (Cons (Car (Var 0))
                                  ((Var 2) (Cdr (Var 0)))))
            (Var 1)))))
   Nil).

Fixpoint delete v l :=
  match l with
    | nil => nil
    | x :: l' => if val_eq_dec v x then delete v l'
                                   else x::delete v l'
  end.

Inductive delete_spec : Spec cfg :=
  delete_claim : forall v l pl env, exp_val delete_spec
    delete_body (pl::fix_env (Lam delete_body) (v::env))
    (rep_list l pl) (rep_list (delete v l)).
                   
Lemma delete_proof : sound lam_step delete_spec.
Proof. list_solver.
simpl;destruct (val_eq_dec v v0);list_run. Qed.