Require Import list_examples.

Definition omega_comb := (Lam ((Var 0) (Var 0))) (Lam ((Var 0) (Var 0))).

Definition omega_inf_cfg env s m k :=
  {|
    code := Exp ((Var 0) (Var 0)) (Env (Closure ((Var 0) (Var 0)) (Env env) :: env));
    heap := s;
    mark := m;
    ctx := k
  |}.

Inductive omega_spec : Spec cfg :=
  | omega_claim : forall env P,
      exp_val omega_spec omega_comb env P (fun _ => constraint False)
  | omega_rec : forall env s m k,
      omega_spec (omega_inf_cfg env s m k) (fun c => False).

Lemma omega_proof : sound lam_step omega_spec.
Proof. list_solver; contradiction. Qed.
