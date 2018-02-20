Require Import patterns.
Require Import proof.
Require Import lambda.

Definition fix_env (body:exp) (env0:list val) : list val :=
  Closure (((Var 1) (Var 1)) (Var 0))
    (Env (Closure strict_worker
           (Env (Closure body (Env env0)::nil))::nil))
  ::env0.
Definition evals F m k post : cfg -> Prop :=
  fun c' => match c' with
    | Cfg (Val v) s' m' k' =>
      s' |= post v :* litP F /\ k' = k /\ (m' >= m)%Z
    | _ => False
  end.

Definition exp_val (R : Spec cfg) c e pre post :=
  forall s F m k, s |= pre :* litP F ->
  R (Cfg (Exp c (Env e)) s m k) (evals F m k post).