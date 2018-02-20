Require Import String.
Require Import ZArith.

Require Import imp.

Set Implicit Arguments.

Local Open Scope string.
Local Open Scope Z.

Local Coercion con : Z >-> exp.
Local Coercion var : string >-> exp.

Definition zero_loop : stmt :=
  while (le 1 "x") (assign "x" (plus "x" (-1))).

Definition sum_loop : stmt :=
  while (not (eql (postdec "n") 0)) (assign "s" (plus "s" "n")).

Require Import Recdef.
Function sum_to (x : Z) {wf (fun a b => -1 <= a < b) x} : Z :=
  (if Z.ltb x 0 then 0 else x + sum_to (x-1))%Z.
Proof.
intro x. rewrite Z.ltb_ge. auto with zarith.
apply Z.lt_wf.
Qed.

Definition env_eq (e1 e2 : Env) := forall x, e1 x = e2 x.

Lemma test_execution : forall e,
  let e0 := set (set e "n" 3) "s" 0 in
  exists e', 
    (exists n, trc step_s n (sum_loop, e0) (skip, e'))
  /\ env_eq e' (set (set e "n" (e' "n")) "s" 3).
intros. repeat eexists.
repeat (progress (repeat (eapply step;[solve[eauto using step_s, step_b, step_e]|]));instantiate;simpl).
eapply done.
reflexivity.

subst e0.
intro x.
unfold set.
repeat match goal with [ |-context[?H]] =>
  match H with (if _ then ?A else ?B) => change H with A || change H with B end
  end.
destruct (string_dec "n" x). subst. reflexivity.
destruct (string_dec "s" x). subst. reflexivity.
reflexivity.
Qed.