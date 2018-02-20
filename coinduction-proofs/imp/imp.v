Require Import String.
Require Import ZArith.

Set Implicit Arguments.

Local Open Scope Z.

(* Defining a simple imperative language *)

Inductive exp :=
  | var : string -> exp
  | con : Z -> exp
  | plus : exp -> exp -> exp
  | postdec : string -> exp
  .

Inductive bexp :=
  | bcon : bool -> bexp
  | eql : exp -> exp -> bexp
  | le : exp -> exp -> bexp
  | not : bexp -> bexp
  | and : bexp -> bexp -> bexp
  .

Inductive stmt :=
  | assign : string -> exp -> stmt
  | skip : stmt
  | seq : stmt -> stmt -> stmt
  | cond : bexp -> stmt -> stmt -> stmt
  | while : bexp -> stmt -> stmt
  .

Definition Env := string -> Z.
Definition set env x (v:Z) :=
  fun x' => if string_dec x x' then v else env x'.
Arguments set env !x v !x' / .
  (* "simpl" should reduce set if concrete values are given for both variables *)

Notation cong_l op R1 R2 :=
  (forall a env a' env', R1 (a,env) (a',env') ->
   forall b, R2 (op a b, env) (op a' b, env')).
Notation cong_1 op R1 R2 :=
  (forall a env a' env', R1 (a,env) (a',env') -> R2 (op a, env) (op a', env')).
Notation cong_r op nf R1 R2 :=
  (forall a, cong_1 (op (nf a)) R1 R2).

Inductive step_e : (exp * Env) -> (exp * Env) -> Prop :=
  | eval_var : forall v env, step_e (var v, env) (con (env v), env)
  | cong_plus_l : cong_l plus step_e step_e
  | cong_plus_r : cong_r plus con step_e step_e
  | eval_plus : forall v1 v2 env,
     step_e (plus (con v1) (con v2), env) (con (v1 + v2), env)
  | eval_postdec : forall x env,
     step_e (postdec x, env) (con (env x), set env x (env x - 1))
  .
Inductive step_b : (bexp * Env) -> (bexp * Env) -> Prop :=
  | eval_le : forall v1 v2 env, step_b (le (con v1) (con v2), env) (bcon (Z.leb v1 v2), env)
  | cong_le_l : cong_l le step_e step_b
  | cong_le_r : cong_r le con step_e step_b
  | eval_eq : forall v1 v2 env, step_b (eql (con v1) (con v2), env) (bcon (Z.eqb v1 v2), env)
  | cong_eq_l : cong_l eql step_e step_b
  | cong_eq_r : cong_r eql con step_e step_b
  | eval_not : forall b env, step_b (not (bcon b), env) (bcon (negb b), env)
  | cong_not : cong_1 not step_b step_b
  | eval_and : forall b e env, step_b (and (bcon b) e, env) (if b then e else bcon false, env)
  | cong_and : cong_l and step_b step_b
  .

Inductive step_s : (stmt * Env) -> (stmt * Env) -> Prop :=
  | exec_assign : forall x v env, step_s (assign x (con v),env) (skip, set env x v)
  | cong_assign : forall x, cong_1 (assign x) step_e step_s
  | exec_seq : forall s env, step_s (seq skip s,env) (s,env) 
  | cong_seq : cong_l seq step_s step_s
  | exec_cond : forall b s1 s2 env, step_s (cond (bcon b) s1 s2, env) (if b then s1 else s2, env)
  | cong_cond : forall b b' env env' s1 s2, step_b (b,env) (b',env') ->
      step_s (cond b s1 s2,env) (cond b' s1 s2,env')
  | exec_while : forall b s env, step_s (while b s,env) (cond b (seq s (while b s)) skip, env)
  .

(* transitive-reflexive closure *)
Inductive trc {A : Set} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
  | done : forall a b, a = b -> trc R 0 a b
  | step : forall a b, R a b -> forall n c, trc R n b c -> trc R (S n) a c.

Definition map_trc {A : Set} {R1 R2 : A -> A -> Prop} (f : forall a b, R1 a b -> R2 a b) :
  forall n a b, trc R1 n a b -> trc R2 n a b.
Proof. induction 1;econstructor (eauto). Qed.