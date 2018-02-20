Require Import graph.
Require Import ZArith.
Set Implicit Arguments.

Require Import String.
Require Import schorr_waite.

(* may need new representation predicate storing also the address of the node? *)

Inductive tree :=
  | Node : Z -> tree -> tree -> tree
  | Leaf.
Inductive ltree :=
  | LNode : Z -> Z -> ltree -> ltree -> ltree
  | LLeaf.
Definition ltree_addr t :=
  match t with
    | LNode p _ _ _ => p
    | LLeaf => 0
  end.

Fixpoint rep_ltree (t : ltree) : MapPattern k k :=
  match t with
  | LLeaf => emptyP
  | LNode p v l r =>
      (constraint (p <> 0) :* p h|-> tree_node v (ltree_addr l) (ltree_addr r)
       :* rep_ltree l :* rep_ltree r)%pattern
  end.

Fixpoint isConst v t :=
  match t with
    | LLeaf => True
    | LNode _ n l r => n = v /\ isConst v l /\ isConst v r
  end.

Fixpoint mark m t :=
  match t with
    | LLeaf => LLeaf
    | LNode p _ l r => LNode p m (mark m l) (mark m r)
  end.

Inductive isWellMarkedPath : ltree -> Prop :=
  | path1 : forall p l r,
     isConst 0 l -> isWellMarkedPath r -> isWellMarkedPath (LNode p 1 l r)
  | path2 : forall p l r,
     isConst 3 r -> isWellMarkedPath l -> isWellMarkedPath (LNode p 2 l r)
  | path_leaf : isWellMarkedPath LLeaf
  .

Inductive isWellMarked' (q : ltree) : ltree -> Prop :=
  | marked0 : forall p l r, isConst 0 l -> isConst 0 r ->
       isWellMarkedPath q -> isWellMarked' q (LNode p 0 l r)
  | marked1 : forall p l r, isConst 3 q -> isConst 0 l ->
       isWellMarkedPath r -> isWellMarked' q (LNode p 1 l r)
  | marked2 : forall p l r, isConst 3 r -> isConst 3 q ->
       isWellMarkedPath l -> isWellMarked' q (LNode p 2 l r)
  | marked_leaf : isConst 3 q -> isWellMarked' q LLeaf
  .

Definition isWellMarked a t := isWellMarked' t a.

Fixpoint proj0 t :=
  match t with
    | LLeaf => Leaf
    | LNode p _ l r => Node p (proj0 l) (proj0 r)
  end.
Fixpoint mark3 t :=
  match t with
    | Leaf => LLeaf
    | Node p l r => LNode p 3 (mark3 l) (mark3 r)
  end.

Fixpoint restorePathPointers t q :=
  match q with
    | LNode p 1 l r => restorePathPointers (Node p t (proj0 l)) r
    | LNode p 2 l r => restorePathPointers (Node p (proj0 r) t) l
    | LNode _ _ _ _ => Leaf (* An error, I think *)
    | LLeaf => t
  end.

Fixpoint restorePointers p q :=
  match p with
  | LNode i 0 l r => restorePathPointers (Node i (proj0 l) (proj0 r)) q
  | LNode i 1 l r => restorePathPointers (Node i (proj0 q) (proj0 l)) r
  | LNode i 2 l r => restorePathPointers (Node i (proj0 r) (proj0 q)) l
  | LNode i 3 l r => restorePathPointers (Node i (proj0 l) (proj0 r)) q
  | LNode _ _ _ _ => Leaf (* shouldn't hit this *)
  | LLeaf => proj0 q
  end.

(* Overall claim:
   rule <k> $ => return; ...</k>
         <heap>... swtree(root)(T) => swtree(root)(?T) ...</heap>
    if isConst(0, marks(T)) /\ isConst(3, marks(?T))
       /\ pointers(T) = pointers(?T) *)
(* Loop invariant:
   inv <heap>... swtree(p)(?TP), swtree(q)(?TQ) ...</heap>
          /\ isWellMarked(?TP, ?TQ)
          /\ pointers(T) = restorePointers(?TP, ?TQ) *)

Inductive schorr_waite_spec : Spec kcfg :=
  schorr_waite_claim : forall c,
  kcell c = kra schorr_waite_code kdot ->
  forall t, store c ~= "root" s|-> KInt (ltree_addr t) ->
  forall hframe, heap c |= rep_ltree t :* hframe ->
    isConst 0 t ->
  schorr_waite_spec c (fun c' => exists rest,
          kcell c' = kra SReturnVoid rest
          /\ stk_equiv (stack c) (stack c')
          /\ functions c ~= functions c'
          /\ heap c' |= rep_ltree (mark 3 t) :* hframe)
| schorr_waite_loop_claim :
  forall c rest, kcell c = kra schorr_waite_loop rest ->
  forall r t p q, store c ~= "root" s|-> r :* "t" s|-> t
                  :* "p" s|-> KInt (ltree_addr p) :* "q" s|-> KInt (ltree_addr q) ->
  isWellMarked p q ->
  forall hframe, heap c |= rep_ltree p :* rep_ltree q :* hframe ->
  schorr_waite_spec c (fun c' =>
          kcell c' = rest
          /\ stk_equiv (stack c) (stack c')
          /\ functions c ~= functions c'
          /\ heap c' |= rep_ltree (mark3 (restorePointers p q)) :* hframe).

Lemma schorr_waite_proof : sound kstep schorr_waite_spec.
start_proving;(eapply sstep;[step_solver|]).

* (* Overall goal *)

graph_run.

+ (* Early exit at zero tree *)
destruct t; simpl in * |- *;simplify_pat_hyps.
exfalso. 
  exfalso; tauto.
  clear e.
 apply ddone. done_solver.

+ (* With nonzero value, have nonempty tree *)
eapply dtrans.
trans_solver.
instantiate (1:=LLeaf).
equate_maps.
(* bash on the isWellMarked precondition *)
  destruct t. simpl in * |- *. intuition. subst.
  constructor. assumption. assumption. constructor.
  constructor. simpl. constructor.
pat_solver.

simpl. intros. repeat use_graph_cfg_assumptions; simpl in * |- *.

eapply dstep. step_solver.
eapply ddone. done_solver.

match goal with 
  [H : context [mark3 (restorePointers t LLeaf)] |- _] =>
  replace (mark3 (restorePointers t LLeaf)) with (mark3 (proj0 t)) in H;
  [replace (mark3 (proj0 t)) with (mark 3 t) in H|]
end.

assumption.

clear. induction t;simpl;congruence. 

revert H2. clear.
induction t;simpl;intuition;subst;simpl;congruence.

* (* Loop goal *)

graph_run.

+ (* exits loop *)
destruct p;simpl in *|-*;simplify_pat_hyps;subst.
congruence.
clear e.
inversion_clear H1.

apply ddone;done_solver.
Lemma mark_id : forall t, isConst 3 t -> mark3 (proj0 t) = t.
induction t;simpl;intuition;congruence.
Qed.
rewrite mark_id by assumption.
break_join;[eassumption|eassumption|equate_maps].

+
(* progress into loop, needs help seeing that p
  is not a non-leaf tree so load can succeed *)

destruct p;simpl in n;[|congruence].
simpl in *|-*;simplify_pat_hyps.

graph_run.

- (* in true case because mark reached 3 *)
assert (z0 = 2) by auto with zarith.
subst z0; clear e.
inversion_clear H1.

simpl Zplus.
eapply dtrans. trans_solver.
equate_maps. instantiate (1:=(LNode z 3 p2 q)). equate_maps.

Lemma well_marked_from_path : forall p q,
  isWellMarkedPath p -> isConst 3 q -> isWellMarked p q.                             intros.
inversion_clear H;constructor;try assumption.
Qed.
apply well_marked_from_path;simpl;tauto.


pat_solver.

(* Now need to finish up after passing things ... *)
simpl.

intros. apply ddone. 
progress decompose record H1;clear H1.
repeat split;try assumption.

match goal with
[H : context [(restorePointers p1 (LNode z 3 p2 q))] |- _] =>
replace (restorePointers p1 (LNode z 3 p2 q))
   with (restorePathPointers (Node z (proj0 p2) (proj0 q)) p1)
     in H
end.
assumption.

clear -H6 H7 H8.
destruct p1;[|simpl;auto].
inversion_clear H8;reflexivity.

- (* In false case because left subtree was leaf *)

destruct p1;
[exfalso;simpl in H4;simplify_pat_hyps;simpl in e;tauto
|].
simpl in * |- *. clear e. progress simplify_pat_hyps.

eapply dtrans.
eapply schorr_waite_loop_claim with (q:=LLeaf);simpl.
reflexivity.
equate_maps. instantiate (1:=r). instantiate (1:=LNode z (z0+1) p2 q).
equate_maps.

unfold isWellMarked.
inversion H1;subst.
unfold isWellMarked in H1.
constructor;trivial.
constructor;trivial.
destruct n0;reflexivity.

simpl. pat_solver.

(* Now we need to use the transitivity result *)
simpl.

intros.
apply ddone.
progress decompose record H6;clear H6.
done_solver.

inversion H1;subst;simpl in H12;assumption.

- { (* Counter not 3, left not null.
       Need to help it realize the tree exists so we
       can load the subtree mark *)

destruct p1;[|destruct n1;reflexivity].
simpl in * |- *.
simplify_pat_hyps.

graph_run.
(* In true branch because left subtree exists and has key zero *)

- eapply dtrans.
  eapply schorr_waite_loop_claim;simpl.

reflexivity.

equate_maps.
instantiate (1:=LNode z1 z2 p1_1 p1_2).
instantiate (1:=LNode z (z0+1) p2 q).
equate_maps.

unfold isWellMarked. inversion H1;subst;simpl in *|-*.
decompose record H11. constructor;try assumption;constructor;assumption.
decompose record H13. constructor;try assumption;constructor;assumption.
destruct n0;reflexivity.

pat_solver.

(* Now use result *)
simpl in * |- *. intros. apply ddone.
progress decompose record H8;clear H8.
done_solver.

inversion H1;subst;simpl in H14.
assumption.
assumption.
destruct n0;reflexivity.

- (* Last case - false branch of if because left child mark not 0,
     even though root still 3 *)

(* Um, shouldn't this be impossible on a tree? *)
exfalso.

inversion H1;subst;simpl in *|-*.
decompose record H11. congruence.
decompose record H13. congruence.
congruence.
}

Qed.
