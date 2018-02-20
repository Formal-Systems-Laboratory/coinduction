Require Import Ring.

Require Export himp_steps.
Require Export himp_syntax_sugar.

Require Export fun_domains_props.

Require Export proof.
Require Export proof_automation.
Require Import patterns.
Require Import equate_map_reflection.
Require Export himp_claims.

Open Scope string_scope.
Open Scope list_scope.

Set Implicit Arguments.

(* Some lemmas used in proof automation *)

Lemma use_value_heap : forall ret krest store stack frame funs mark
           (Q : Spec kcfg) (P : kcfg -> Prop),
  (forall r' store' heap' funs' mark',
    heap' |= ret r' :* litP frame ->
    store' ~= store ->
    funs' ~= funs ->
    (mark' >= mark)%Z ->
    Q (KCfg (kra r' krest) store' stack heap' funs' mark') P
   ) ->
  (forall k', value_heap ret krest store stack frame funs mark k' -> Q k' P).
Proof. destruct k'. destruct 1. intuition. subst. auto. Qed.

Lemma use_return_heap : forall ret stack frame funs mark
           (Q : Spec kcfg) (P : kcfg -> Prop),
  (forall r' krest store' heap' funs' mark',
    heap' |= ret r' :* litP frame ->
    funs' ~= funs ->
    (mark' >= mark)%Z ->
    Q (KCfg (kra (SReturn r') krest) store' stack heap' funs' mark') P
   ) ->
  (forall k', return_heap ret stack frame funs mark k' -> Q k' P).
Proof. destruct k'. simpl.
let H := fresh in intro H;decompose record H;clear H.
subst. auto.
Qed.

Arguments stk_equiv s1 s2 : simpl nomatch.

(** Register it as an equivalence relations,
    mostly just so we can say "reflexivity" *)
Lemma stk_equiv_refl : forall s, stk_equiv s s.
Proof.
induction s;simpl;auto.
destruct a. simpl. auto using equivRefl.
Qed.

Lemma stk_equiv_sym : forall s1 s2, stk_equiv s1 s2 -> stk_equiv s2 s1.
Proof.
induction s1;destruct s2;simpl;firstorder.
destruct a;trivial.
destruct a,f;firstorder.
Qed.

Lemma stk_equiv_trans : forall s1 s2 s3,
  stk_equiv s1 s2 -> stk_equiv s2 s3 -> stk_equiv s1 s3.
Proof.
induction s1.
destruct s2;intros. assumption. destruct H.

destruct s2.
intros. destruct a. simpl in H. destruct H.
intros. destruct s3. destruct f. simpl in H0. destruct H0.
destruct a.
destruct f.
destruct f0.
simpl in * |- *.
intuition.
congruence.
equate_maps.
eauto.
Qed.

Add Relation (list Frame) stk_equiv
  reflexivity proved by stk_equiv_refl
  symmetry proved by stk_equiv_sym
  transitivity proved by stk_equiv_trans
  as stk_equiv_rel.

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
Ltac hyp_check :=
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

Ltac generic_solver trans_tac step_solver done_solver split_stuck :=
  start_proving;(eapply sstep;[solve [step_solver]|]);
  generic_run trans_tac step_solver done_solver split_stuck.
