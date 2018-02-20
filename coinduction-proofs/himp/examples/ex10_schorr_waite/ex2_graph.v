(*
 * The specification of the function states that the heap contains the graph of
 * the structure nodes reachable from the root pointer. All the nodes that are
 * not reachable from the root are part of the heap frame. Each node of the
 * mathematical Schorr-Waite graph is labeled with the pair
 * (pointer_to_structure, mark), while each edge is labeled with name of the
 * field that generated the respective edge. In this context, pointers(T)
 * refers to the graph holding only the pointer label (dropping the mark label
 * from each node), while marks(T) refers to the graph holding only the mark
 * component. The specification also states that the mark labels of the initial
 * graph are 0, and that the pointer labels of the initial and final graph are
 * identical.
 * 
 * The loop invariant states that the heap contains the graph of the structure
 * nodes reachable from p and q. The isRestorable predicate encodes the
 * existence of a path from p to root in the initial graph and the nodes on
 * that path are marked accordingly. The invariant also states that the pointer
 * structure of the initial graph can be obtain by restoring the edges in the
 * current graph, and that the root program variable remains unchanged.
 * 
 * A few words about notation: {Elements}s stands for the set with the Elements
 * content, while graph(Roots)(Graph) stands for the graph of structure nodes
 * reachable starting from an address in Roots and stopping at a the 0 (NULL)
 * address. For the definitions and axioms required by this proof see [1].
 *)

(* Graph predicate claims whole graph is reachable *)

Require Import ZArith.
Require Import List.

Require Import graph.
Require Import schorr_waite.

Set Implicit Arguments.

(* Represent a graph reachable from a single point by the
   depth-first traversal, as a tree with backlinks allowed *)
Inductive dfs_tree (zs : list Z) : list Z -> Set :=
  | Null : dfs_tree zs zs
  | Ref : forall z, In z zs -> dfs_tree zs zs
  | Node : forall phere zs' zs'', ~In phere zs ->
      dfs_tree (phere::zs) zs' -> dfs_tree zs' zs''
      -> dfs_tree zs zs''.
Inductive dfs_tree_ctx (ls : list Z)
  : list Z -> list Z -> list Z -> Set :=
  | LeftOf : forall phere ls' rs rs' rs'', ~In phere ls'
    -> dfs_tree_ctx ls ls' rs' rs'' -> dfs_tree rs rs'
    -> dfs_tree_ctx ls (phere::ls') rs rs''
  | RightOf : forall phere ls' ls'' rs rs', ~In phere ls'
    -> dfs_tree (phere::ls') ls'' -> dfs_tree_ctx ls ls' rs rs'
    -> dfs_tree_ctx ls ls'' rs rs'
  | Top : forall rs, dfs_tree_ctx ls ls rs rs.
Fixpoint plug {ls ls' rs rs'} (c : dfs_tree_ctx ls ls' rs rs')
  : dfs_tree ls' rs ->  dfs_tree ls rs' :=
  match c with
  | LeftOf phere _ _ _ _ n path r =>
       fun t => plug path (@Node _ phere _ _ n t r)
  | RightOf phere _ _ _ _ n l path =>
       fun t => plug path (@Node _ phere _ _ n l t)
  | Top _ => fun t => t
  end.

Definition dfs_tree_addr {zs} {zs'} (t : dfs_tree zs zs') : Z :=
  match t with
    | Null => 0%Z
    | Ref addr _ => addr
    | Node addr _ _ _ _ _ => addr
  end.
Fixpoint rep_dfs_tree (v : Z) {zs} {zs'} (t : dfs_tree zs zs')
    : MapPattern k k :=
  match t with
    | Null => emptyP
    | Ref z _ => emptyP
    | Node p _ _ _ l r => constraint (p <> 0) :*
        p h|-> tree_node v (dfs_tree_addr l) (dfs_tree_addr r)
         :* rep_dfs_tree v l :* rep_dfs_tree v r
  end%pattern.

Definition dfs_tree_ctx_addr {ls ls' rs rs'}
  (c : dfs_tree_ctx ls ls' rs rs') : Z :=
  match c with
  | LeftOf phere _ _ _ _ _ _ _ => phere
  | RightOf phere _ _ _ _ _ _ _ => phere
  | Top _ => 0%Z
  end.
Fixpoint rep_dfs_ctx {ls ls' rs rs'}
  (ctx : dfs_tree_ctx ls ls' rs rs') : MapPattern k k :=
  match ctx with
  | Top _ => emptyP
  | LeftOf phere _ _ _ _ _ path rtree =>
        constraint (phere <> 0)
     :* phere h|-> tree_node 1 (dfs_tree_addr rtree)
                               (dfs_tree_ctx_addr path)
     :* rep_dfs_ctx path :* rep_dfs_tree 0 rtree 
  | RightOf phere _ _ _ _ _ ltree path =>
        constraint (phere <> 0)
     :* phere h|-> tree_node 2 (dfs_tree_ctx_addr path)
                               (dfs_tree_addr ltree)
     :* rep_dfs_tree 3 ltree :* rep_dfs_ctx path
end%pattern.

(* At some points in the loop, q points at the path and
   p at an unmarked (non-Ref, non-Null) tree. At other points,
    p is at the root of the path and q is holding one of the
   finished subtrees of that node *)
Definition isWellMarked (descending : bool) (p q : Z)
   {ls ls' rs rs'} (tree : dfs_tree ls' rs)
  (path : dfs_tree_ctx ls ls' rs rs') : Prop :=
  if descending then p <> 0
  /\ match tree with  Node _ _ _ _ _ _ => True | _ => False end
  /\   p = dfs_tree_addr tree /\ q = dfs_tree_ctx_addr path
  else p = dfs_tree_ctx_addr path /\ q = dfs_tree_addr tree.

Inductive schorr_waite_spec : Spec kcfg :=
  schorr_waite_claim : forall c,
  kcell c = kra schorr_waite_code kdot ->
  forall {zs'} (t : dfs_tree nil zs'),
    store c ~= "root" s|-> KInt (dfs_tree_addr t) ->
  forall hframe, heap c |= rep_dfs_tree 0 t :* hframe ->
  schorr_waite_spec c (fun c' => exists rest,
          kcell c' = kra SReturnVoid rest
          /\ stk_equiv (stack c) (stack c')
          /\ functions c ~= functions c'
          /\ heap c' |= rep_dfs_tree 3 t :* hframe)
  | schorr_waite_loop_claim : forall c rest,
  kcell c = kra schorr_waite_loop rest ->
  forall r t p q, store c ~= "root" s|-> r :* "t" s|-> t
                         :* "p" s|-> KInt p :* "q" s|-> KInt q ->
  forall descending {ls' rs rs'} tree
         (path : dfs_tree_ctx nil ls' rs rs'),
  isWellMarked descending p q tree path -> forall hframe,
  heap c |= rep_dfs_tree (if descending then 0 else 3) tree
         :* rep_dfs_ctx path :* hframe ->
  schorr_waite_spec c (fun c' =>
          kcell c' = rest
          /\ stk_equiv (stack c) (stack c')
          /\ functions c ~= functions c'
          /\ heap c' |= rep_dfs_tree 3 (plug path tree) :* hframe).

Lemma rep_tree_values :
  forall {ls ls'} (d : dfs_tree ls ls') heap v,
  heap |= rep_dfs_tree v d ->
  forall p,
  In p ls' ->
    (p <> 0 /\ exists l r heap', heap ~= p h|-> tree_node v l r :* heap')
    \/ In p ls.
induction d;intros heap v H; simpl in H;simplify_pat_hyps.
(* Null *)
auto.
(* Rep *)
auto.
(* Node *)
specialize (IHd1 _ _ H0).
specialize (IHd2 _ _ H1).
intros p Hin.
specialize (IHd2 p Hin).

destruct IHd2 as [IHd2 | IHd2].
decompose record IHd2.
left. split;[assumption|repeat eexists;equate_maps].

clear Hin.
specialize (IHd1 _ IHd2).

destruct IHd1 as [IHd1 | IHd1].
decompose record IHd1.
left. split;[assumption|repeat eexists;equate_maps].

destruct IHd1.
subst p.
left. split;[assumption|repeat eexists;equate_maps].

right. assumption.
Qed.

Lemma rep_values :
  forall {ls' rs rs'} (path : dfs_tree_ctx nil ls' rs rs') heap,
  heap |= rep_dfs_ctx path ->
  forall p, In p ls' -> p <> 0
     /\ exists v l r heap', heap ~= p h|-> tree_node v l r :* heap'
            /\ v <> 0.
induction path; intros heap H p;simpl in H;simplify_pat_hyps.
(* Left Of *)
destruct 1. subst;split;[assumption|repeat eexists;[equate_maps|discriminate]].
specialize (IHpath _ H0 _ H2).
   decompose record IHpath;clear IHpath.
   split;[assumption|repeat eexists;[equate_maps|assumption]].
(* Right Of *)
specialize (IHpath _ H1).
intro HIn.
apply (rep_tree_values _ _ _ H0) in HIn.
destruct HIn.
 (* maybe in the left tree *)
   decompose record H2;clear H2.
   split;[assumption|repeat eexists;[equate_maps|discriminate]].
 (* If not, either in the exposed node or in the tree *)
 destruct H2.
  subst phere.
  split;[assumption|repeat eexists;[equate_maps|discriminate]].
 specialize (IHpath _ H2).
 decompose record IHpath;clear IHpath.
  split;[assumption|repeat eexists;[equate_maps|assumption]].
(* Top *)
destruct 1.
Qed.

Lemma schorr_waite_proof : sound kstep schorr_waite_spec.
start_proving;(eapply sstep;[step_solver|]).

* (* Overall goal *)

graph_run.

+ (* exiting on null tree *)
apply ddone;done_solver.
destruct t;simpl in * |- *;simplify_pat_hyps;
[pat_solver|exfalso;tauto..].

+ (* transitivity past the loop *)

eapply dtrans.
eapply schorr_waite_loop_claim with (descending:=true) (path:=@Top _ _);
simpl;work_trans_goal.
(* t has to be a Node here, the pointer is nonzero and
   the left context is nil *)
destruct t;tauto.

(* now continue after the trans *)
destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
subst.
simplify_pat_hyps.
 
eapply dstep. step_solver.
apply ddone. simpl;done_solver.

* (* loop claim *)

graph_run.

+ (* exiting because tree is zero *)
apply ddone;simpl;done_solver.

(* Desending must be false *)
destruct descending;[destruct H1;exfalso;tauto|].
simpl in H1.
(* So, the p=0 comes from the path, which must be Top.
   The other alternatives are refuted by unfolding the
   rep_dfs_ctx predicate to get a "phere <> 0" constraint. *)
destruct H1. destruct path; simpl in H2, H1;simplify_pat_hyps.
destruct H1;exfalso;tauto.
destruct H1;exfalso;tauto.

simpl.
fold (rep_dfs_tree 3 tree).
pat_solver.  

+ (* p is nonzero, need to help see that there's
     a tree node at address p.
     Actually go a bit farther and split into
     cases based on descending and the path and stuff.
   *)

destruct descending;simpl in H1.

- (* If we're descending, p must be a literal node *)
progress decompose record H1; clear H1.
destruct tree;try (exfalso;assumption);[idtac].

(* Expand assumptions a bit now that we know it's a Node *)
simpl in H.
simpl in * |- *;simplify_pat_hyps.

subst p.
repeat match goal with
[H1 : phere <> 0, H2 : phere <> 0 |- _] => clear H1
end.

graph_run.

{
destruct tree1;[clear e| exfalso..].
Focus 2.
(* backreferences can't be null, by the
   rep_values lemma or by pointing to an exposed node *)
simpl in e.
destruct  i. congruence.
destruct (rep_values _ _ H2 _ i). congruence.
Focus 2.
(* Nodes assert they are non-null as part of the representation
  predicate *)
simpl in e. simpl in H1. simplify_pat_hyps. congruence.

simpl in * |- *;simplify_pat_hyps.

eapply dtrans.
eapply schorr_waite_loop_claim with (descending:=false) (tree:=(Null _))
   (path:=(LeftOf phere n0 path tree2))
  ;simpl;work_trans_goal.

subst q.
pat_solver.

(* past the transitivity, should be done *)
intros;apply ddone;assumption.
}

{
   (* left tree non-null,
      so we need to demonstrate it has a mark to read
     *)
subst q.
destruct tree1;[destruct n;reflexivity| |].

+ (* In the ref case it will be nonzero, and we'll skip  *)
inversion i.
- (* loops right back to the current node, which is already exposed *)
  subst z;simplify_pat_hyps.
  graph_run.
  (* Around, ready to return *)
  eapply dtrans.
  eapply schorr_waite_loop_claim with (descending:=false)
     (tree:=(Ref _ _ i))
     (path:=(LeftOf phere n0 path tree2))
    ;simpl;work_trans_goal.

  destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
  simpl in * |-*; simplify_pat_hyps.
  apply ddone;done_solver.
  
- (* loops to an earlier node, need to use rep_values lemma *)
  destruct (rep_values _ _ H2 _ H).
  simpl in * |- *.
  progress decompose record H8;clear H8.
  simplify_pat_hyps.

  graph_run.
  (* Now we need to drop the extra map equality before it confuses
     anything *)
  rewrite H9 in * |- *; clear x1 H9.

  (* ready for transitivity *)
  eapply dtrans.
  eapply schorr_waite_loop_claim with (descending:=false)
     (tree:=(Ref (phere :: ls') z i))
     (path:=(LeftOf phere n0 path tree2))
    ;simpl;work_trans_goal.

  break_join;[eassumption| |equate_maps].
  pat_solver.

  destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
  simpl in * |- *;simplify_pat_hyps.
  apply ddone;done_solver.

+ (* In the node case it will be marked zero, and we'll enter *)
  simpl in * |- *. simplify_pat_hyps.

  graph_run.

  eapply dtrans.
  change (~In phere0 (phere::ls')) in n1.
  eapply schorr_waite_loop_claim with (descending:=true)
     (tree:=(Node n1 tree1_1 tree1_2))
     (path:=(LeftOf phere n0 path tree2))
    ;simpl;work_trans_goal.

  destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
  simpl in * |- *;simplify_pat_hyps.
  apply ddone;done_solver.
}

-
  (* Here p is a node on the path and we are ascending.
     We'll split into two cases -
     in "RightOf" we'll have the mark go up to three and ascend.
     in "LeftOf", we have to examine the left subtree as in other cases,
      seeing if it's null, or marked with a zero/nonzero mark.
     *)

destruct H1.
destruct path;simpl in *|-*;[| |exfalso;congruence];simplify_pat_hyps.

{
(* In LeftOf, we'll have to examine the subtree and decide whether to enter. *)
subst p q.

graph_run.

- (* Pointer was zero, must have been a leaf *)
eapply dtrans.
eapply schorr_waite_loop_claim with (descending:=false)
     (tree:=d)
     (path:=(RightOf n0 tree path));simpl;work_trans_goal.
destruct d. simpl. pat_solver.
simpl. pat_solver.
simpl in H6;simplify_pat_hyps. simpl in e. exfalso;tauto.

destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
simpl in * |- *;simplify_pat_hyps.
apply ddone;done_solver.

destruct d.
apply emptyP_expose in H6. rewrite H6, equivUnit. assumption.
apply emptyP_expose in H6. rewrite H6, equivUnit. assumption.
simpl in H6; simplify_pat_hyps. exfalso. tauto.

-
  (* Nonzero, couldn't be leaf. Need to show that
     we can look up the mark. *)

destruct d.
destruct n1;reflexivity.

+
  (* Is a ref, use the lemmas to show the lookup will succeed and
     return a non-zero mark *)

(* (Ref rs z i) *)
simpl.
assert (exists v' l' r' heap',
phere h|-> tree_node 2 (dfs_tree_ctx_addr path) (dfs_tree_addr tree)
  :* x2 :* x3 :* x0 :* x ~= z h|-> tree_node v' l' r' :* heap' /\ v' <> 0).

assert (phere h|-> tree_node 2 (dfs_tree_ctx_addr path) (dfs_tree_addr tree) :* x0 :* x
       |= rep_dfs_ctx (RightOf n0 tree path)) by pat_solver.
destruct (rep_values _ _ H1 _ i).
progress decompose record H7;clear H7.
do 4 eexists. split.
  rewrite (equivComAssoc _ x2).  rewrite (equivComAssoc _ x3).
  rewrite H8.
  solve[equate_maps].
  assumption.

progress decompose record H1;clear H1.
eapply dstep;[step_solver|].
graph_run.

eapply dtrans.
eapply schorr_waite_loop_claim with (descending:=false)
     (tree:=(Ref rs z i))
     (path:=(RightOf n0 tree path));simpl;work_trans_goal.
rewrite <- H4; clear x6 H4.
pat_solver.

destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
simpl in * |- *;simplify_pat_hyps.
apply ddone;done_solver.

+ (* Is a node, unfold rep predicates to show it will be marked zero *)
simpl in * |- *;simplify_pat_hyps.

graph_run.

eapply dtrans.
eapply schorr_waite_loop_claim with (descending:=true)
     (tree:=(Node n2 d1 d2))
     (path:=(RightOf n0 tree path));simpl;work_trans_goal.

  destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
  simpl in * |- *;simplify_pat_hyps.
  apply ddone;done_solver.

}

{
(* In the RightOf case, the count will hit 3 and we ascend *)
subst.
graph_run.

eapply dtrans.
eapply schorr_waite_loop_claim with
  (descending:=false) (tree:=Node n0 d tree) (path:=path)
  ;simpl;work_trans_goal.

destruct k';simpl;let H := fresh in intro H;progress decompose record H;clear H.
simpl in * |- *;simplify_pat_hyps.
apply ddone;done_solver.
}
Qed.
