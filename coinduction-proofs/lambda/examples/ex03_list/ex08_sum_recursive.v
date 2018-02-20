Require Import list_examples.

Definition sum_body :=
  If (Var 0) (Let (Deref (Var 0)) (Lam
    (Plus (Car (Var 0)) ((Var 2) (Cdr (Var 0))))))
    (Num 0).

Fixpoint num_list l := match l with
  | nil => True
  | Num _ :: l' => num_list l'
  | _ => False
  end.
Fixpoint nsum l := match l with
  | nil => 0
  | Num n :: l' => n + nsum l'
  | _ => 0
  end.

Inductive sum_spec : Spec cfg :=
  sum_claim : forall H l r env, exp_val sum_spec
  sum_body (r::fix_env (Lam sum_body) env)
    (asP H (rep_list l r) :* constraint (num_list l))
    (fun v => constraint (v = Num (nsum l)) :* litP H).

Lemma sum_proof : sound lam_step sum_spec.
Proof. list_solver. Qed.