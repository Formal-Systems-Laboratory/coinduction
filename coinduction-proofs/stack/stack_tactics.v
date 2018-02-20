Require Export stack.
Require Export proof.
Require Export proof_automation.

Require Import patterns.
Require Import equate_map_reflection.

Set Implicit Arguments.

(* Generic proof automation for the stack langanguage *)

Ltac step_solver := econstructor (simpl;solve[trivial|reflexivity|equate_maps|ring]);idtac.

(* The tactic trans_applies succeed if there is any claim in the set of
   claims being proved whose expectation for the kcell matches the current code
 *)
Ltac trans_applies := econstructor(
  match goal with [|- code _ = _] => reflexivity || fail 1 | _ => idtac end).

(* The transitivity tactic tries to apply any claim whose preconditions
   can be met as a transitivity.
   If one applies, it uses the supplied "trans_use_result" tactic to extract hypothesis
   from the conclusion, and get the goal back into the form of a simple
   "dtrans" claim for further proof search.
   (if trans_use result tactic succeeds but doesn't get things into the right form,
   execution will be paused at that point (with the transitivity already taken)
   for the user to do it, because trying to automatically take another step will fail.

   If no claim applies, it then checks for a claim that matches the current
   code but couldn't be used automatically, and pauses for the user
   (assuming that the claim should work, and the prover just failed).

   Otherwise, it returns to the main proof search tactic.   
 *)
Ltac trans_solver := econstructor(simpl;
  solve [reflexivity|auto with zarith|equate_maps]).

Ltac trans_use_result := idtac.

Ltac trans_tac :=
  eapply dtrans;[solve[trans_solver] || (trans_applies;idtac "pausing for trans";fail 1)|]
  ;try trans_use_result. (* if trans_solver succeeded, we commit to the transitivity *)

Lemma Zneq_bool_cases x y :
  if Zneq_bool x y then x <> y else x = y.
Proof. unfold Zneq_bool;destruct (Z.compare_spec x y)
;auto with zarith. Qed.

Ltac split_bool B :=
  match B with
    | (?x <? ?y)%Z => pose proof Zlt_cases x y;destruct B
    | (?x <=? ?y)%Z => pose proof Zle_cases x y;destruct B
    | Zneq_bool ?x ?y => pose proof Zneq_bool_cases x y;destruct B
    | (?x =? ?y)%Z =>
        first[replace B with true
          by (symmetry;apply Z.eqb_eq; (auto with zarith || ring || omega))
             |replace B with false
          by (symmetry;apply Z.eqb_neq; (auto with zarith || ring || omega))
             |destruct (Z.eqb_spec x y)]
    | (negb ?B') => split_bool B'
  end.

Ltac split_tac :=
  simpl;
  match goal with
  | [|- if ?B then _ else _ ] => split_bool B
  end;idtac.

Ltac done_solver := simpl;repeat split;try reflexivity;auto with zarith.

Ltac use_cfg_assumptions :=
  match goal with 
    | [H : code ?v = _ |- _] =>
      is_var v; destruct v; simpl in * |- ;
      rewrite H in * |- *;clear H
    | [H : _ /\ _  |- _ ] => destruct H
    | [H : ?l ~= _ |- ?G] =>
         match G with
         | context [?l] => fail 1
         | _ => is_var l;rewrite H in * |- *;clear H l
         end
   end.

Ltac start_proving :=
  let get_cfg_assumptions := (intros;repeat use_cfg_assumptions) in
  get_cfg_assumptions;apply proved_sound;destruct 1;
  simpl in * |-;get_cfg_assumptions.

Ltac generic_solver trans_tac step_solver done_solver split_stuck :=
  start_proving;(eapply sstep;[solve [step_solver]|]);
  generic_run trans_tac step_solver done_solver split_stuck.