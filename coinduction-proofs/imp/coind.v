Require Import String.
Require Import ZArith.

Require Import imp.
Require Import proof.
Require Import example.

Set Implicit Arguments.

Local Open Scope Z.
Local Open Scope string.

Definition env_eq (e1 e2 : Env) := forall x, e1 x = e2 x.

Arguments set env !x v !x' / .

Inductive zero_loop_spec : Spec (stmt * Env) :=
  zero_loop_claim : forall env, 0 <= env "x" ->
  zero_loop_spec (zero_loop,env)
    (fun cfg' => fst cfg' = skip /\ env_eq (snd cfg') (set env "x" 0)).

Ltac env_eq_tac := intro x;repeat match goal with [H : env_eq _ _ |- _] => specialize (H x) end;
  unfold set in * |- *;repeat match goal with [|-context[string_dec ?a ?b]] =>
  destruct (string_dec a b);[subst|] end;try congruence.
Ltac run := repeat first[eapply dtrans;[constructor(simpl;omega) || (constructor;fail 1)|]
      |eapply ddone;simpl;split;[congruence|try (env_eq_tac;omega)]
      |eapply dstep;[solve[eauto using step_s,step_b,step_e]|]].

Lemma zero_loop_ok : sound step_s zero_loop_spec.
apply proved_sound;destruct 1.
eapply sstep;[solve[eauto using step_s]|].
run.
destruct (Z.leb_spec 1 (env "x"));simpl;run.
destruct 1;run.
Qed.

Inductive sum_loop_spec : Spec (stmt * Env) :=
  sum_loop_claim : forall env, 0 <= env "n" ->
  sum_loop_spec (sum_loop,env)
    (fun cfg' => fst cfg' = skip /\
      env_eq (snd cfg')
             (set (set env "n" (snd cfg' "n")) "s" (env "s" + sum_to (env "n" - 1)))).

Lemma sum_loop_ok : sound step_s sum_loop_spec.
apply proved_sound;destruct 1.
eapply sstep;[solve[eauto using step_s]|].
run.
destruct (Z.eqb_spec (env "n") 0);simpl;run.
(* when n = 0, loop exited *)
env_eq_tac. rewrite e. rewrite sum_to_equation, sum_to_equation;simpl. auto with zarith.
(* continued around and applied the transitivity *)
destruct k';simpl;destruct 1;subst. run.
env_eq_tac. rewrite H1;revert H n;clear.
repeat match goal with [|- context[env ?v]] => generalize (env v);intro end;intros.
rewrite (sum_to_equation (z - 1));destruct (Z.ltb_spec (z-1) 0);auto with zarith.
Qed.