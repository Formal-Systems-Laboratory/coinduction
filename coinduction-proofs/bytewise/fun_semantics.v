Require Import String.
Require Import List.
Require Import ZArith.
Require Import Ring.

Require Export fun_domains_props.
Require Export fun_domains_sugar.
Require Export fun_steps.
Require Export proof.
Require Import patterns.
Require Import equate_map_reflection.

Open Scope string_scope.

Set Implicit Arguments.

(* Z-indexed map entries *)
Notation "x 'h|->' y" := (mapItem (kra (KInt x) kdot) (kra (y : kitem) kdot))
  (at level 50, no associativity) : Map.
Notation "x 'h|->' y" := (itemP (kra (KInt x) kdot) (kra (y : kitem) kdot))
  (at level 50, no associativity) : MapPattern.

Definition set_kcell kcell c :=
  match c with
    | KCfg _     store stack heap functions =>
      KCfg kcell store stack heap functions
  end.
Definition set_heap c heap :=
  match c with
    | KCfg k env stack _    functions =>
      KCfg k env stack heap functions
  end.

(* A basic property of the step relation, then proof automation *)
Lemma kstep_resp_kequiv_fwd : forall k1 k1' k2,
  kequiv k1 k1' -> kstep k1 k2 -> (exists k2', kstep k1' k2').
intros.
destruct H0, k1'; simpl in H; decompose record H;clear H;subst;
try solve[eexists;econstructor(eassumption || reflexivity || equate_maps)];

(* Each Return needs to inspect stack *)
(destruct stack;try solve [exfalso;assumption];
 match goal with [H : stk_equiv _ (?p :: _) |- _] =>
    destruct p; simpl in H; decompose record H;clear H
 end);eexists;econstructor (eassumption).
Qed.

(** Now proof automation *)

Create HintDb step_hints discriminated.
Create HintDb done_hints discriminated.
(* f_equal ? *)
Hint Resolve stk_equiv_refl : step_hints done_hints.
Hint Extern 2 (_ ~= _) => equate_maps : step_hints done_hints.
Hint Extern 1 (@eq Z ?l ?r) =>
  (has_evar l;fail 1) || (has_evar r;fail 1) || solve[ring] : step_hints done_hints.
Ltac step_solver := econstructor (solve[simpl;try reflexivity;eauto with step_hints]);idtac.

(* The tactic trans_applies succeed if there is any claim in the set of
   claims being proved whose expectation for the kcell matches the current code
 *)
Ltac trans_applies := econstructor(
  match goal with [|- kcell _ = _] => reflexivity || fail 1 | _ => idtac end).

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
  solve [reflexivity
  |auto with zarith
  |equate_maps]).

Ltac trans_use_result := idtac.

Ltac trans_tac :=
  eapply dtrans;[solve[trans_solver] || (trans_applies;idtac "pausing for trans";fail 1)|]
  ;try trans_use_result. (* if trans_solver succeeded, we commit to the transitivity *)

(*
  We evaluation becomes stuck on a symbolic boolean constant, we need to make
  a case distinction on whether the constant is true or false so evaluation can
  proceed, but we also need to add some new hypothesis(es) recording the fact
  that the symbolic conclusion was true or false, in case the condition tested
  will be important for finishing the proof later.

  This handling might need to be refined a bit to work nicely with the predicates
  needed in a particular specification, but some basic cases corresponding to
  the boolean expressions in the language seems to work pretty well for now.
 *)
Ltac split_bool B :=
  match B with
    | (?x <? ?y)%Z => pose proof Zlt_cases x y;destruct B
    | (?x <=? ?y)%Z => pose proof Zle_cases x y;destruct B
    | (?x =? ?y)%Z =>
        first[replace B with true
          by (symmetry;apply Z.eqb_eq; (auto with zarith || ring || omega))
             |replace B with false
          by (symmetry;apply Z.eqb_neq; (auto with zarith || ring || omega))
             |destruct (Z.eqb_spec x y)]
    | (negb ?B') => split_bool B'
  end.

(*
  The positions where evaluation may be stuck on a symbolic constant
  are purely a function of the language. These could perhaps be computed
  automatically by comparing evaluation rules.
 *)
Ltac split_tac :=
  simpl;
  match goal with
  | [|- trans _ _ {| kcell := kra (KStmt (SIf (BCon ?B) _ _)) _ |} _ ] =>
    split_bool B
  | [|- trans _ _ {| kcell := kra (KExp (BAnd (BCon ?B) _)) _ |} _ ] =>
    split_bool B
  end;idtac.

Ltac done_solver := simpl;repeat split;try reflexivity;auto with done_hints zarith.

Ltac use_cfg_assumptions :=
  match goal with 
    | [H : kcell ?v = _ |- _] =>
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

(* Pause execution if we ever end up with
   a map equation between two variables,
   or a non-decomposed pattern hypothesis *)
(*
Ltac hyp_check ::=
  match goal with
(*
 | [H : ?l ~= ?r |- _] => is_var l; is_var r
   We can end up with irreducible equations between map variables,
   if both are used in the goal, in places where we don't (yet)
   know how to do setoid rewriting by ~=.

   Especially happens with transitivity.   

   Maybe just being able to rewrite in the current
   configuration of "trans" would allow eliminating most of these?
 *)
  | [H : (_ :* _) |= _ |- _] => idtac
  | [H : _ |= _ :* _ |- _] => idtac
  | [H : _ |= _ |-> _ |- _] => idtac
  | [H : _ |= emptyP |- _] => idtac
  end;fail 1.
*)

Require Export proof_automation.

Ltac generic_solver trans_tac step_solver done_solver split_stuck :=
  start_proving;(eapply sstep;[solve [step_solver]|]);
  generic_run trans_tac step_solver done_solver split_stuck.
