Require Import list_examples.

Definition omega_cfg env s m k :=
     {|
     code := Exp ((Var 0) (Var 0)) (Env (Closure ((Var 0) (Var 0)) (Env env) :: env));
     heap := s;
     mark := m;
     ctx := k |}.

Inductive omega_spec : Spec cfg :=
  omega_claim : forall F env s m k,
    omega_spec (omega_cfg env s m k) (evals F m k (fun _ : val => constraint False)).

Lemma omega_proof : sound lam_step omega_spec.
Proof.
  list_solver. contradiction. Grab Existential Variables. assumption.
Qed.
