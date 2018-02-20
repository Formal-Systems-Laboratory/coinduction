Require Export fun_semantics.
Require Export patterns.
Require Export pattern_tactics.

Set Implicit Arguments.

Require Import ZArith.
Require Import List.

Require Import zipper_patterns.
Require Import Setoid.

Arguments Zplus x y : simpl nomatch.

(* Claim that calls evaluate to values, instead of claiming that
   function bodies evaluate to return statements? *)

(* Operations we'll implement for concrete linked lists *)
Fixpoint zlength {A} (l : list A) :=
  match l with
    | nil => 0%Z
    | _ :: l' => (1 + zlength l')%Z
  end.
Definition sum : list Z -> Z := fold_right Zplus 0%Z.

(** A list node in memory *)
(*
Notation list_node val next := (KStruct (Struct ("val" s|-> KInt val :* "next" s|-> KInt next))).
(** And some abbreviations for code working with list nodes *)
Notation arr_val v := (EProject (ELoad (EVar v)) "val").
Notation arr_next v := (EProject (ELoad (EVar v)) "next").
Notation build_node v p := (EBuild ("val" s|-> v :* "next" s|-> p)).
 *)

(** Representing lists in memory

    The more general predicate describes a chain of list node ending
    at a specified pointer.

    Complete non-circular lists are a special case where the tail pointer
    is zero.
 *)
Fixpoint rep_seg (val : list Z) (tailptr : Z) (p : Z) : MapPattern k k :=
 (match val with
    | nil => constraint (p = tailptr%Z)
    | x :: xs => constraint (p <> 0%Z) :*
        (existsP (p' : Z),
           (p h|-> x :* (p + 1) h|-> p'
             :* rep_seg xs tailptr p'))
  end)%pattern.
Notation rep_list l p := (rep_seg l 0%Z p).

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

Definition returns_list c l rest_heap : kcfg -> Prop :=
  (fun c' =>
        match get_returning c' with
          | Some v' =>
              heap c' |= rep_list l v' :* litP rest_heap
              /\ returning (set_heap c (heap c'))  v' c'
          | _ => False
        end).

Lemma use_returns_list : forall ckcell cstore cstk cheap cfunctions
     l rest_heap (Q : kcfg -> (kcfg -> Prop) -> Prop) (P : kcfg -> Prop),
  (forall v kstore kheap kfunctions,
    kheap |= rep_list l v :* litP rest_heap ->
    cfunctions ~= kfunctions ->
   forall kstk,
    stk_equiv cstk kstk ->
   forall krest,
    Q (KCfg (kra (KStmt (SReturn (ECon v))) krest)
            kstore kstk kheap kfunctions) P
   ) ->
  (forall k', returns_list
     (KCfg ckcell cstore cstk cheap cfunctions)
    l rest_heap k' -> Q k' P).
intros.
pose proof (get_returning_returns k').
unfold returns_list in H0.
destruct (get_returning k');[|exfalso;assumption].
destruct H1.
destruct k'.
simpl in H1; subst.
simpl in * |- *.
intuition.
Qed.

Lemma return_list_patterns_equivalent : forall c l rest_heap k,
  (exists v, returning_heap_pat c (rep_list l v :* litP rest_heap) v k) <->
  returns_list c l rest_heap k.

destruct c;destruct k;(split;[destruct 1|intro H;unfold returns_list in H]);
(simpl in H;
repeat match type of H with
| (match ?x with _ => _ end) => destruct x;try solve [exfalso;exact H]
| _ /\ _ => let H' := fresh in destruct H as [H' ?]
end;[idtac]);
subst;
[unfold returns_list|eexists];simpl;
repeat split;try (assumption || reflexivity).
Qed.

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
  instantiate; repeat (simpl_list_rep || simplify_pat_hyps || (progress simpl in * |-)).

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
  | _ => assumption
  end.

Lemma rep_seg_exp_cons :
  forall e p x l,
    PatEquiv (rep_seg (x::l) e p)
      (constraint (p <> 0%Z)
       :* existsP (next:Z), p h|-> x :* (p+1) h|-> next :* rep_seg l e next).
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
     | context [p h|-> _] => rewrite (rep_seg_exp_cons e p)
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
| [|- Int _ = Int _] => apply f_equal;ring
| [|- KInt _ = KInt _] => apply f_equal;ring
| [|- ECon _ = ECon _] => apply f_equal;ring
| [|- _ = _] => reflexivity || ring
| [|- stk_equiv _ _] => solve [assumption | apply stk_equiv_refl]
| [|- _ ~= _] => solve[equate_maps]
| [|- _ |= _] => instantiate;simpl;pat_solver
| _ => auto
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
  [|- fun_domains_aux.kcell _ = _ ] => reflexivity || fail 1 | _ => idtac end);
  simpl;
  match goal with
    | [|- exists _ , _ ] => eexists;work_trans_goal
    | [|- _ /\ _] => split;work_trans_goal
    | [|- _ |= _] => instantiate;simpl;pat_solver
    | _ => simpl;try eassumption;try reflexivity;try auto with zarith;
                  try equate_maps
  end).

Create HintDb trans_simpl discriminated.
Hint Rewrite Z.add_0_r : trans_simpl.

Ltac trans_use_result :=
  try solve[intros;eapply ddone;assumption]
  || ((apply use_returning;do 5 intro;try use_expose_frame;intros)
  || (apply use_returns_list;do 6 intro;try use_expose_frame;intros))
  ; use_assumptions
  .
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