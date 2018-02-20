Require Export himp_claims.
Require Export himp_tactics.
Require Export patterns.
Require Export pattern_tactics.

Set Implicit Arguments.

Require Import ZArith.
Require Import List.

Require Import zipper_patterns.
Require Import Setoid.

Arguments Zplus x y : simpl nomatch.

Notation tree_node val left right :=
  (KStruct (Struct ("val" s|-> KInt val :* "left" s|-> KInt left :* "right" s|-> KInt right))).
Notation build_tree val left right :=
  (EBuild ("val" s|-> (val : Exp) :* "left" s|-> (left : Exp) :* "right" s|-> (right : Exp))).

(* And now stuff about proving *)

Create HintDb graph_hints discriminated.
Hint Resolve f_equal stk_equiv_refl : graph_hints.
Hint Extern 2 (_ ~= _) => equate_maps : graph_hints.
Hint Extern 1 (Int _ = Int _) => (apply f_equal;solve[ring]) : graph_hints.

Ltac step_solver := econstructor (solve[simpl;eauto with graph_hints]).

Ltac use_graph_cfg_assumptions :=
  match goal with 
    | [H : kcell ?v = _ |- _] =>
      is_var v; destruct v; simpl in H;
      rewrite H in * |- *;clear H
    | [H : _ = kcell ?v |- _] =>
      is_var v; destruct v; simpl in H;
      rewrite <- H in * |- *;clear H
    | [H : exists _ , _ |- _] =>
      decompose record H; clear H
    | [H : _ /\ _  |- _ ] => destruct H
    | [H : ?l ~= _ |- ?G] =>
         match G with
         | context [?l] => fail 1
         | _ => is_var l;rewrite H in * |- *;clear H l
         end
   end.

Ltac use_assumptions :=
  instantiate; simpl in * |- *; simplify_pat_hyps; simpl in * |- *.

Ltac start_proving ::=
  let get_cfg_assumptions := (intros;repeat use_graph_cfg_assumptions) in
  try get_cfg_assumptions;apply proved_sound;destruct 1;
         simpl in * |-;try (get_cfg_assumptions;simpl in * |- *);
    use_assumptions.

(* Maybe we need a tactic that's given the new hypothesis
   and figures out how to apply it? *)
Ltac split_tac :=  instantiate;simpl;match goal with
  | [|- trans _ _ {| kcell := kra (KStmt (SIf (BCon ?B) _ _)) _ |} _ ] =>
    split_bool B
  | [|- trans _ _ {| kcell := kra (KExp (BAnd (BCon ?B) _)) _ |} _ ] =>
    split_bool B
  | [|- trans _ _ {| kcell := kra (KExp (BOr (BCon ?B) _)) _ |} _ ] =>
    split_bool B
  end;try (exfalso;solve[auto]);use_assumptions.

(* pattern solver *)

Lemma exP_lift : forall {Key Elt A} (body : A -> MapPattern Key Elt) P,
  PatEquiv (exP body :* P) (exP (fun a => body a :* P)%pattern).
firstorder.
Qed.
Lemma exist_expose : forall Key Elt A (m : A -> MapPattern Key Elt) h,
   (h |= existP a, m a) <-> (exists a, h |= m a).
Proof.
reflexivity.
Qed.

Ltac break_join := eexists;eexists;split;[|split].

(* Prove h' |= item for some subheap h' of h *)
Ltac solve_atomic_pat h item :=
  match item with
  | constraint _ => esplit;[auto with zarith | reflexivity]
  | litP _ => apply litP_expose;(reflexivity || equate_maps)
  | itemP _ _ => apply itemP_expose;reflexivity
  | emptyP => apply emptyP_expose;reflexivity
  | _ =>
    match goal with
    [H : ?hp |= item |- _] =>
    match h with
      | context [hp] => eexact H
    end
    end
  end.

Ltac pat_solver :=
match goal with
| [|- ?h |= _] => expand_map h
end;simpl;
repeat (rewrite ?patEquivAssoc;
match goal with
| [|- _ |= existP _ , _] => eexists
| [|- _ |= (existP _ , _) :* _] => rewrite exP_lift
| [|- _ |= asP _ _] => split;[reflexivity|]
| [|- ?h |= ?P :* _] => break_join;[solve_atomic_pat h P| |solve[equate_maps]]
| [|- ?h |= ?P] => solve_atomic_pat h P
| [|- ?h |= ?P] => first[is_evar P | is_var P];
  try eassumption;
  (apply litP_expose; reflexivity) (* make a litP pattern *)
end).

Ltac trans_applies := econstructor(match goal with
  [|- kcell _ = _ ] => reflexivity || fail 1 | _ => idtac end).
Ltac work_trans_goal :=
  lazymatch goal with
    | [|- exists _ , _ ] => eexists;work_trans_goal
    | [|- _ /\ _] => split;work_trans_goal
    | [|- _ |= _] => instantiate;simpl;pat_solver
    | [|- _ ~= _] => instantiate;simpl;equate_maps
    | _ => simpl;try eassumption;try reflexivity;auto with zarith
  end. (* ;instantiate;pat_solver.*)
Ltac trans_solver := econstructor(match goal with
  [|- himp_cfg_and_prims.kcell _ = _ ] => reflexivity || fail 1 | _ => idtac end);
  simpl;work_trans_goal.

Ltac trans_use_result ::=
    try solve[intros;eapply ddone;assumption]
 || lazymatch goal with
    | [|- forall k, returning _ _ k -> _] =>
         apply use_returning;do 8 intro;try use_expose_frame;intros
    | _ => (* try to handle generically *)
         simpl in * |- *;intros;
         repeat use_graph_cfg_assumptions;simpl in * |- *;subst;
         try match goal with
          | [H : stk_equiv (_ :: _) ?stk |- _] => is_var stk;revert stk H;use_expose_frame;intros
         end
    end
    ; use_assumptions.

Create HintDb trans_simpl discriminated.
Hint Rewrite Z.add_0_r : trans_simpl.

Ltac trans_tac :=
  eapply dtrans;[solve[trans_solver] || (trans_applies;fail 1)|];
    try (instantiate;simpl;autorewrite with trans_simpl;trans_use_result).

Ltac stk_equiv_trans_solver l :=
  reflexivity ||
  match goal with [H : stk_equiv l ?m |- _] =>
    apply stk_equiv_trans with m;[exact H|stk_equiv_trans_solver m]
  end.
Ltac done_solver :=
try red;
subst;simpl;
repeat match goal with
| [|- exists _, _ ] => eexists
| [|- _ /\ _] => split
end;
(simpl;match goal with
| [|- Int _ = Int _] => apply f_equal;ring
| [|- KInt _ = KInt _] => apply f_equal;ring
| [|- ECon _ = ECon _] => apply f_equal;ring
| [|- _ = _] => reflexivity || congruence || ring
| [|- stk_equiv ?l _] => stk_equiv_trans_solver l
| [|- _ ~= _] => solve[equate_maps]
| [|- _ |= _] => instantiate;simpl;pat_solver
| _ => auto with zarith
end).

Ltac solve_done_solver :=
try red;
subst;simpl;
repeat match goal with
| [|- exists _, _ ] => eexists
| [|- _ /\ _] => split
end;
solve[simpl;match goal with
| [|- Int _ = Int _] => apply f_equal;ring
| [|- KInt _ = KInt _] => apply f_equal;ring
| [|- ECon _ = ECon _] => apply f_equal;ring
| [|- _ = _] => reflexivity || congruence || ring
| [|- stk_equiv ?l _] => stk_equiv_trans_solver l
| [|- _ ~= _] => solve[equate_maps]
| [|- _ |= _] => instantiate;simpl;pat_solver
| _ => auto with zarith
end].

Ltac graph_step   := generic_step   trans_tac step_solver                   split_tac.
Ltac graph_run    := generic_run    trans_tac step_solver solve_done_solver split_tac.

Ltac graph_solver := generic_solver trans_tac step_solver solve_done_solver split_tac.
