Require Import lambda.
Require Import maps.
Require Import patterns.
Require Import pattern_tactics.
Require Import proof.
Require Import ZArith.
Require Import proof_automation.
Require Import List.

Require Import list_predicates.

Lemma list_seg_app :
  forall l1 l2 p_tl p_mid p_hd h1 h2 h,
  h1 |= list_seg l1 p_mid p_hd ->
  h2 |= list_seg l2 p_tl p_mid ->
  h ~= h1 :* h2 ->
    h |= list_seg (l1++l2) p_tl p_hd.
Proof.
induction l1;simpl;intros;simplify_pat_hyps.
subst. rewrite H1. assumption.
subst.
exists x.
Ltac break_join := eexists;eexists;split;[|split].
break_join;[split;reflexivity| |equate_maps].
exists x2.
break_join;[apply itemP_expose;reflexivity| |equate_maps].
eapply IHl1. eassumption. eassumption. equate_maps.
Qed.

Lemma list_seg_exp_cons :
  forall e p x l,
    PatEquiv (list_seg (x::l) e (Addr p))
       (existsP (next : val), p |-> Pair x next :* list_seg l e next).
Proof.
split;simpl;intros.
simplify_pat_hyps. eexists.
break_join;[apply itemP_expose;reflexivity| |equate_maps].
eassumption. injection H. intro. subst. reflexivity.

exists p.
break_join;[split;reflexivity| |equate_maps].
assumption.
Qed.
Lemma list_seg_exp_app :
  forall a z l1 l2,
    PatImpl
      (existsP mid, list_seg l1 mid a :* list_seg l2 z mid)
      (list_seg (l1++l2) z a).
Proof.
unfold PatImpl;intros.
simplify_pat_hyps.
eauto using list_seg_app.
Qed.

Ltac solve_atomic_pat h item :=
  match item with
  | constraint _ => esplit;[trivial | reflexivity]
      (* Assumes the property is available as a hypothesis *)
  | litP _ => apply litP_expose;(reflexivity || equate_maps)
  | itemP _ _ => apply itemP_expose;reflexivity
  | list_seg ?l ?p ?p => unify l (@nil val);split;reflexivity
  | list_seg _ _ ?p =>
    match  goal with
    | [H : ?hp |= list_seg _ _ p |- _] =>
      match h with
        | context [hp] => eexact H
      end
    end
  | asP _ ?P => split;[reflexivity|];solve_atomic_pat h P
  | _ => assumption
  end.

Ltac simpl_pat h P :=
match P with
| list_seg _ ?e (Addr ?p) =>
   match h with
     | context [p |-> _] => rewrite (list_seg_exp_cons e p)
   end
| list_seg (_ ++ _) ?q ?p => rewrite <- (list_seg_exp_app p q)
| list_seg ?l ?x ?y =>
  (is_evar x;fail 1) || (is_evar y;fail 1) ||
  first [
    match h with
    | context [(y h|-> Pair ?v x)%pattern] =>
    unify l (v::nil);simpl
    end
  | match goal with
    | [H : ?h2 |= list_seg ?l1 ?mid y |- _] =>
      match h with
      | context [h2] => rewrite <- (list_seg_exp_app y x)
      end
    end
  ]
end;simpl.

Lemma exP_lift : forall {Key Elt A} (body : A -> MapPattern Key Elt) P,
  PatEquiv (exP body :* P) (exP (fun a => body a :* P)%pattern).
firstorder.
Qed.

Ltac pat_solver :=
match goal with
| [|- ?h |= _] => expand_map h
end;
repeat (rewrite ?patEquivAssoc;
match goal with
| [|- _ |= existsP _ , _] => eexists
| [|- _ |= (existsP _ , _) :* _] => rewrite exP_lift
| [|- _ |= asP _ _] => split;[reflexivity|]
| [|- ?h |= ?P :* _] => break_join;[solve_atomic_pat h P| |solve[equate_maps]]
                     || simpl_pat h P
| [|- ?h |= ?P] =>
   solve_atomic_pat h P || simpl_pat h P
| [|- ?h |= ?P] => first[is_evar P | is_var P];
  try eassumption;
  (apply litP_expose; reflexivity) (* make a litP pattern *)
end).


Ltac simpl_list_rep :=
match goal with
 |[H : _ |= list_seg ?l _ Nil |- _] => 
   destruct l;simpl in H;simplify_pat_hyps;[clear H|exfalso;congruence]
 |[H : _ |= list_seg ?l _ ?p, Hnz : ?p <> Nil |- _] =>
   destruct l;simpl in H;simplify_pat_hyps;[exfalso;congruence|subst p;clear Hnz]
end.

Ltac use_list_cfg_assumptions :=
  match goal with
    | [c := _ : cfg |- _] => unfold c; clear c
    | [H : _ /\ _  |- _ ] => destruct H
    | [H : Addr _ = Addr _ |- _] => injection H;clear H;intro;subst
    | [H : match ?v with Nil => False | _ => _ end |- _] =>
       destruct v;try (exfalso;exact H);[idtac]
  end.

(*
  match goal with 
    | [H : code ?v = _ |- _] =>
      is_var v; destruct v; simpl in H;
      rewrite H in * |- *;clear H
    | [H : exists _ : Map _ _ , _ |- _] =>
      decompose record H; clear H
    | [H : ?l ~= _ |- ?G] =>
         match G with
         | context [?l] => fail 1
         | _ => is_var l;rewrite H in * |- *;clear H l
         end
   end. *)

Ltac use_assumptions :=
  instantiate; repeat (simpl_list_rep || simplify_pat_hyps
                   || use_list_cfg_assumptions || (progress simpl in * |-));
  try subst.

Ltac start_proving :=
  let get_cfg_assumptions := (intros;repeat (use_list_cfg_assumptions
                                            || simpl_list_rep)) in
  try get_cfg_assumptions;apply proved_sound;destruct 1;
         simpl in * |-;try (get_cfg_assumptions;simpl in * |- *);
    use_assumptions.

Create HintDb step_hints discriminated.
Create HintDb done_hints discriminated.
(* f_equal ? *)
Hint Extern 2 (_ ~= _) => equate_maps : step_hints done_hints.
(*
Hint Extern 1 (@eq Z ?l ?r) =>
  (has_evar l;fail 1) || (has_evar r;fail 1) || solve[ring] : step_hints done_hints.
 *)
Ltac step_solver := econstructor (solve[simpl;try reflexivity;eauto with step_hints]);idtac.

Ltac generic_solver trans_tac step_solver done_solver split_stuck :=
  start_proving;(eapply sstep;[solve [step_solver]|]);
  generic_run trans_tac step_solver done_solver split_stuck.


Ltac trans_solver := econstructor(auto;pat_solver;auto with zarith).
(*
match goal with
  [|- code _ = _ ] => reflexivity || fail 1 | _ => idtac end);
  simpl;
  match goal with
    | [|- exists _ , _ ] => eexists;work_trans_goal
    | [|- _ /\ _] => split;work_trans_goal
    | [|- _ |= _] => instantiate;simpl;pat_solver;auto with zarith
    | _ => simpl;try eassumption;try reflexivity;try auto with zarith;
                  try equate_maps
  end).
 *)

Ltac use_evals :=
  let k := fresh "k" in let H := fresh in
  intros k H;
  let code := fresh in let ctx := fresh in destruct k as [code ? ? ctx];
  destruct code;[|exfalso;exact H];simpl in H;
  destruct H as (? & ? & ?);subst ctx.

Ltac trans_use_result :=
  try solve[intros;eapply ddone;assumption]
  || use_evals
 (* || use_generic_postcondition *)
  ; use_assumptions.

Ltac trans_tac :=
  eapply dtrans;[solve[trans_solver] || (econstructor;fail 1)|];
    try (instantiate;simpl;trans_use_result).

Ltac done_solver :=
try red;
subst;simpl;
repeat match goal with
| [|- exists _, _ ] => eexists
| [|- _ /\ _] => split
end;
(simpl;repeat match goal with
| [|- _ = _] => reflexivity || ring
| [|- _ ~= _] => solve[equate_maps]
| [|- _ |= _] => instantiate;simpl;pat_solver;auto with zarith
| _ => solve[auto with zarith]
end).

Ltac split_nil v :=
  assert ({v=Nil}+{v<>Nil /\ isNil v = false}) as [->|[]]
   by (destruct v;intuition congruence).
Ltac split_tac :=
  match goal with
  | [|- trans _ _ {| code := Val ?v ; ctx := IfCond _ _ _ _ |} _ ] => split_nil v
  end;eapply dstep;[eapply eval_if_nil;reflexivity|
                   |eapply eval_if_nonnil;assumption|];
  use_assumptions.

Ltac list_solver := generic_solver trans_tac step_solver done_solver split_tac.
Ltac list_run    := generic_run    trans_tac step_solver done_solver split_tac.