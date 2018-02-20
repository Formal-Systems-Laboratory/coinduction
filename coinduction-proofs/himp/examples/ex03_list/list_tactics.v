Require Export himp_tactics.
Require Export patterns.
Require Export pattern_tactics.

Set Implicit Arguments.

Require Export ZArith.
Require Export List.

Require Import zipper_patterns.
Require Import Setoid.

Require Import list_predicates.

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

(* Maybe could do by eauto with right lemmas? *)
let list_rep_tac := repeat esplit;try (eassumption || (try (apply itemP_expose);equate_maps))
in list_rep_tac;eapply IHl1;list_rep_tac.
Qed.

(* Some abbreviations used in writing specifications *)

(** Now we define proof automation for the list examples *)

Require Import ZArith.

Create HintDb heap_list_hints discriminated.
Hint Resolve f_equal stk_equiv_refl : heap_list_hints.
Hint Extern 2 (_ ~= _) => equate_maps : heap_list_hints.
Hint Extern 1 (Int _ = Int _) => (apply f_equal;solve[ring]) : heap_list_hints.

Ltac step_solver := econstructor (solve[simpl;eauto with heap_list_hints]).

Ltac simpl_list_rep :=
match goal with
 |[H : _ |= rep_seg ?l _ ?p, H0 : ?p = 0%Z |- _] => 
   destruct l;simpl in H;simplify_pat_hyps;[clear H0|exfalso;tauto]
 |[H : _ |= rep_seg ?l _ ?p, Hnz : ?p <> 0%Z |- _] =>
   destruct l;simpl in H;simplify_pat_hyps;[exfalso;tauto|clear Hnz]
end.

Ltac use_assumptions :=
  instantiate; repeat (simpl_list_rep || simplify_pat_hyps || (progress simpl in * |-));
  try subst.

Ltac split_tac :=  simpl;match goal with
  | [|- trans _ _ {| kcell := kra (KStmt (SIf (BCon ?B) _ _)) _ |} _ ] =>
    split_bool B
  | [|- trans _ _ {| kcell := kra (KExp (BAnd (BCon ?B) _)) _ |} _ ] =>
    split_bool B
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

Definition AtomicPatGoal (full_heap matched_heap_var : Map k k) (pat : MapPattern k k)
  := matched_heap_var |= pat.
Definition SimplPatGoal (h : Map k k) (p p_simp : MapPattern k k) := PatImpl p_simp p.
Create HintDb pat_hints discriminated.

Hint Extern 1 (AtomicPatGoal ?h _ (rep_seg ?l ?p' ?p)) =>
  match p' with
  | p => unify l (@nil Z);split;reflexivity
  | _ => match goal with
         | [H : ?hp |= rep_seg _ _ p |- _] =>
           match h with
           | context [hp] => eexact H
           end
         end
  end : pat_hints.

Lemma rep_seg_exp_cons :
  forall e p x l,
    PatEquiv (rep_seg (x::l) e p)
      (constraint (p <> 0%Z)
       :* existsP next, p h|-> list_node x next :* rep_seg l e next).
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

Hint Extern 1 (SimplPatGoal ?h (rep_seg (_ ++ _) ?q ?p) _) =>
  apply (rep_seg_exp_app p q).
Hint Extern 2 (SimplPatGoal ?h (rep_seg _ ?e ?p) _) =>
  match h with
  | context [(p h|-> _)%Map] =>
    apply map_pat_equiv_inverse_impl_subrelation;refine (rep_seg_exp_cons e p _ _)
  end : pat_hints.
Hint Extern 3 (SimplPatGoal ?h (rep_seg ?l ?x ?y) _) =>
  (is_evar x;fail 1) || (is_evar y;fail 1) ||
  first [
    match h with
    | context [y h|-> list_node ?v x] =>
    unify l (v::nil);simpl;reflexivity
    end
  | match goal with
    | [H : ?h2 |= rep_seg ?l1 ?mid y |- _] =>
      match h with
      | context [h2] => apply (rep_seg_exp_app y x)
      end
    end
  ] : pat_hints.

Ltac solve_atomic_pat h item :=
  match item with
  | constraint _ => esplit;[trivial | reflexivity]
      (* Assumes the property is available as a hypothesis *)
  | litP _ => apply litP_expose;(reflexivity || equate_maps)
  | itemP _ _ => apply itemP_expose;reflexivity
  | asP _ ?P => split;[reflexivity|];solve_atomic_pat h P
  | _ => assumption ||
     match goal with [ |- ?c |= _ ] =>
        change (AtomicPatGoal h c item);
          solve[auto with pat_hints]
     end
  end.
Ltac simpl_pat h P :=
   let P' := fresh "P" in evar (P' : MapPattern k k);
   let H := fresh in assert (PatImpl P' P) as H;
   [change (SimplPatGoal h P P');subst P';solve [auto with pat_hints]|
    rewrite <- H;clear H;subst P'];simpl.

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
(simpl;repeat match goal with
| [|- Int _ = Int _] => apply f_equal;ring
| [|- KInt _ = KInt _] => apply f_equal;ring
| [|- ECon _ = ECon _] => apply f_equal;ring
| [|- _ = _] => reflexivity || ring
| [|- stk_equiv _ _] => solve [assumption | apply stk_equiv_refl]
| [|- _ ~= _] => solve[equate_maps]
| [|- _ |= _] => instantiate;simpl;pat_solver;auto with zarith
| _ => solve[auto with zarith]
end).

Ltac trans_applies := econstructor(match goal with
  [|- kcell _ = _ ] => reflexivity || fail 1 | _ => idtac end).
Ltac work_trans_goal :=
  match goal with
    | [|- exists _ , _ ] => eexists;work_trans_goal
    | [|- _ /\ _] => split;work_trans_goal
    | [|- _ |= _] => idtac
    | _ => solve [simpl;try eassumption;try reflexivity;try auto with zarith;
                  equate_maps]
  end. (* ;instantiate;pat_solver.*)
Ltac trans_solver := (econstructor(match goal with
  [|- himp_cfg_and_prims.kcell _ = _ ] => reflexivity || fail 1 | _ => idtac end);
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

Ltac trans_use_result :=
  solve[intros;eapply ddone;assumption] ||
  (  (apply use_returning;do 6 intro;try use_expose_frame;intros)
  || (apply use_value_heap; intros)
  || (apply use_return_heap; intros)
  ) ; use_assumptions.
Ltac trans_tac :=
  eapply dtrans;[solve[trans_solver] || (trans_applies;fail 1)|];
    try (instantiate;simpl;autorewrite with trans_simpl;trans_use_result).

Ltac list_step   := generic_step   trans_tac step_solver             split_tac.
Ltac list_run    := generic_run    trans_tac step_solver done_solver split_tac.

Ltac list_solver := generic_solver trans_tac step_solver done_solver split_tac.

Ltac use_list_cfg_assumptions :=
  match goal with
    | [H : kcell ?v = _ |- _] =>
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
         simpl in * |-;try (get_cfg_assumptions;simpl in * |- *);
    use_assumptions.
