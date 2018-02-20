Require Import zipper_patterns.
Require Import Setoid.
Require Import proof.

Require Import maps.
Require Import List.

Require Import ZArith.
Require Import stack_tactics.
Require Import patterns.
Require Import pattern_tactics.
Require Import claims.

Require Import list_predicates.

(* Proof automation for the list examples *)

Arguments Zplus x y : simpl nomatch.

Lemma rep_seg_app : forall l2 p_tl p_mid h2,
                  h2 |= rep_seg l2 p_tl p_mid ->
                forall l1 p_hd h1,
                  h1 |= rep_seg l1 p_mid p_hd -> 
                forall h,
                  h ~= h1 :* h2 ->
                  h |= rep_seg (l1 ++ l2) p_tl p_hd.
Proof.
induction l1;simpl;intros;simplify_pat_hyps.
rewrite H1;congruence.

(* Discharge the simple stuff *)
let list_rep_tac := repeat esplit;try (eassumption || (try (apply itemP_expose);equate_maps))
in list_rep_tac.
eapply IHl1. eassumption.
equate_maps.
equate_maps.
Qed.

Create HintDb heap_list_hints discriminated.
Hint Resolve f_equal : heap_list_hints.
Hint Extern 2 (_ ~= _) => equate_maps : heap_list_hints.

Ltac step_solver := econstructor (solve[simpl;eauto with heap_list_hints]).

Ltac simpl_list_rep :=
match goal with
 |[H : _ |= rep_seg ?l _ ?p, H0 : ?p = 0%Z |- _] => 
   destruct l;simpl in H;simplify_pat_hyps;[clear H0|exfalso;tauto]
 |[H : _ |= rep_seg ?l _ ?p, Hnz : ?p <> 0%Z |- _] =>
   destruct l;simpl in H;simplify_pat_hyps;[exfalso;tauto|clear Hnz]
end.

Ltac simpl_min_length :=
match goal with
 |[H : match ?l with nil => False | _ :: _ => _ end |- _] =>
  destruct l;[solve[destruct H]|]
 end.

Ltac use_assumptions :=
  instantiate; repeat progress
  (simpl_min_length || simpl_list_rep || simplify_pat_hyps ||
    (progress subst) || (progress simpl in * |-)).

Ltac split_tac := simpl;match goal with
  | [|- trans _ _ {| code := (if ?B then _ else _)++_|} _ ] => split_bool B
  end;try (exfalso;solve[auto]);use_assumptions.

Lemma exP_lift : forall {Key Elt A} (body : A -> MapPattern Key Elt) P,
  PatEquiv (exP body :* P) (exP (fun a => body a :* P)%pattern).
firstorder.
Qed.
Lemma exist_expose : forall Key Elt A (m : A -> MapPattern Key Elt) h,
   (h |= existsP a, m a) <-> (exists a, h |= m a).
Proof.
reflexivity.
Qed.

Ltac break_join := eexists;eexists;split;[|split].

Ltac solve_atomic_pat h item :=
  match item with
  | constraint _ => esplit;[trivial | reflexivity]
      (* Assumes the property is available as a hypothesis *)
  | litP _ => apply litP_expose;(reflexivity || equate_maps)
  | itemP _ _ => apply itemP_expose;reflexivity
  | rep_seg ?l ?p ?p => unify l (@nil Z);split;reflexivity
  | rep_seg _ _ ?p =>
    match  goal with
    | [H : ?hp |= rep_seg _ _ p |- _] =>
      match h with
        | context [hp] => eexact H
      end
    end
  | asP _ ?P => split;[reflexivity|];solve_atomic_pat h P
  | _ => assumption
  end.

Lemma rep_seg_exp_cons :
  forall e p x l,
    PatEquiv (rep_seg (x::l) e p)
      (constraint (p <> 0%Z)
       :* existsP (next:Z), p |-> x :* (p+1) |-> next :* rep_seg l e next).
Proof.
reflexivity.
Qed.
Lemma rep_seg_exp_app :
  forall a z l1 l2,
    PatImpl
      (existsP mid, rep_seg l1 mid a :* rep_seg l2 z mid)
      (rep_seg (l1++l2) z a).
Proof.
unfold PatImpl;intros.
simplify_pat_hyps.
eauto using rep_seg_app.
Qed.

Ltac simpl_pat h P :=
match P with
| rep_seg _ ?e ?p =>
   match h with
     | context [p |-> _ (* v *)] => rewrite (rep_seg_exp_cons e p (* v *))
   end
| rep_seg (_ ++ _) ?q ?p => rewrite <- (rep_seg_exp_app p q)
| rep_seg ?l ?x ?y =>
  (is_evar x;fail 1) || (is_evar y;fail 1) ||
  (*
  first [
    match h with
    | context [y h|-> list_node ?v x] =>
    unify l (v::nil);simpl
    end
  *)
    match goal with
    | [H : ?h2 |= rep_seg ?l1 ?mid y |- _] =>
      match h with
      | context [h2] => rewrite <- (rep_seg_exp_app y x)
      end
    end
end;simpl.

Ltac pat_solver :=
match goal with
| [|- ?h |= _] => expand_map h
end;
repeat (rewrite ?patEquivAssoc;
match goal with
| [|- _ |= emptyP :* _] => rewrite patEquivUnitL
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

Ltac done_solver :=
try red;
subst;simpl;
repeat match goal with
| [|- exists _, _ ] => eexists
| [|- _ /\ _] => split
end;
(simpl;match goal with
| [|- _ = _] => reflexivity || ring
| [|- _ ~= _] => solve[equate_maps]
| [|- _ |= _] => instantiate;simpl;pat_solver;auto with zarith
| _ => auto with zarith
end).

Ltac trans_applies := econstructor(match goal with
  [|- code _ = _ ] => reflexivity || fail 1 | _ => idtac end).
Ltac work_trans_goal :=
  match goal with
    | [|- exists _ , _ ] => eexists;work_trans_goal
    | [|- _ /\ _] => split;work_trans_goal
    | [|- _ |= _] => idtac
    | _ => solve [simpl;try eassumption;try reflexivity;try auto with zarith;
                  equate_maps]
  end. (* ;instantiate;pat_solver.*)
Ltac trans_solver := (econstructor(match goal with
  [|- code _ = _ ] => reflexivity || fail 1 | _ => idtac end);
  simpl;
  match goal with
    | [|- exists _ , _ ] => eexists;work_trans_goal
    | [|- _ /\ _] => split;work_trans_goal
    | [|- _ |= _] => instantiate;simpl;pat_solver;auto with zarith
    | _ => simpl;try eassumption;try reflexivity;try auto with zarith;
                  try equate_maps
  end).

Create HintDb trans_simpl discriminated.
Hint Rewrite Z.add_0_r : trans_simpl.

Ltac use_generic_postcondition :=
  let k := fresh "k" in let H := fresh in
  intros k H; destruct k; progress (decompose record H); clear H; subst.
Ltac trans_use_result :=
  try solve[intros;eapply ddone;assumption]
  || use_generic_postcondition;use_assumptions.

Ltac trans_tac :=
  eapply dtrans;[solve[trans_solver] || (trans_applies;fail 1)|];
    try (instantiate;simpl;autorewrite with trans_simpl;trans_use_result).

Ltac list_step   := generic_step   trans_tac step_solver             split_tac.
Ltac list_run    := generic_run    trans_tac step_solver done_solver split_tac.

Ltac list_solver := generic_solver trans_tac step_solver done_solver split_tac.

Ltac use_list_cfg_assumptions :=
  match goal with 
    | [H : code ?v = _ |- _] =>
      is_var v; destruct v; simpl in H;
      rewrite H in * |- *;clear H
    | [H : exists _ : Map _ _ , _ |- _] =>
      decompose record H; clear H
    | [H : _ /\ _  |- _ ] => destruct H
    | [H : ?l ~= _ |- ?G] =>
         match G with
         | context [?l] => fail 1
         | _ => is_var l;rewrite H in * |- *;clear H l
         end
   end.

Ltac start_proving ::=
  let get_cfg_assumptions := (intros;repeat (use_list_cfg_assumptions
                                            || simpl_list_rep)) in
  try get_cfg_assumptions;apply proved_sound;destruct 1;
         simpl in * |-;subst;try (get_cfg_assumptions;simpl in * |- *);subst;
    use_assumptions.