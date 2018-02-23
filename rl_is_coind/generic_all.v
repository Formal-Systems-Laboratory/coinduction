Require Import generic_soundness.

Require Import reduction.

Require Import proofsystem.
Set Implicit Arguments.

Require Import Setoid.
Require Import Relation_Definitions.

(* For all-path reachability,
   the approximation is indexed by a number of steps, and says that
   every path which terminates within the bound encountered a state
   matching the target state.
 *)

Parameter cfg : Set.
Parameter SF : cfg -> cfg -> Prop.

(* Lemmas *)
Definition nat_pred n n' := n = 1+n'.
Lemma le_iff_clos_nat_pred : forall n m,
                               clos nat_pred false n m <-> m <= n.
Proof.
split.
induction 1.
auto.
unfold nat_pred in H;subst. auto.
eauto with arith.

induction 1.
constructor.
apply clos_trans with m0.
apply clos_step. reflexivity.
assumption.
Qed.

Lemma nat_le_ind : forall (P : nat -> Prop), forall n,
  (forall n0, n0 <= n ->
              (forall n', n0 = 1+n' -> P n') ->
              P n0)
  -> P n.
induction n.
intro H; apply H. constructor. intros. discriminate.
intro H.
apply H.
constructor.
intros.
injection H0;clear H0;intro H0.
subst n'.
auto.
Qed.

Inductive ix_al_reach (P : cfg -> Prop) (c : cfg) : bool -> nat -> Prop :=
  | al_exhausted : forall s, ix_al_reach P c s 0
  | al_here : P c -> forall n, ix_al_reach P c false n
  | al_later : forall n, (exists c', SF c c') ->
                         (forall c', SF c c' -> ix_al_reach P c' false n) ->
                         forall s, ix_al_reach P c s (Datatypes.S n)
  .

Lemma al_reach_unstrict P c n : ix_al_reach P c true n -> ix_al_reach P c false n.
  Proof. destruct 1;constructor;assumption. Qed.

Lemma al_reach_pred P c s n : ix_al_reach P c s (S n) -> ix_al_reach P c s n.
remember (S n) as Sn eqn:HeqSn; intro H; revert n HeqSn; induction H.
(* exhausted *)
discriminate.
(* here *)
constructor;assumption.
(* later *)
intros.
injection HeqSn;clear HeqSn;intro HeqSn.
destruct n0;constructor;auto.
Qed.

Lemma al_reach_impl (P Q : cfg -> Prop) : (forall c, P c -> Q c) -> forall c s n,
                            ix_al_reach P c s n -> ix_al_reach Q c s n.
induction 2;constructor;auto.
Qed.

Require Import Arith.

Lemma min_half_suc (P : nat -> Prop) n m :
  P (S (min n m)) -> P (min n m) -> P (min (S n) m).
Proof.
  destruct (le_lt_dec m n);
  rewrite ?Nat.min_r, ?Nat.min_l by (auto using le_S, le_Sn_le);
  trivial.
Qed.

Lemma al_reach_join P c s1 n1 s2 n2 :
  ix_al_reach (fun c' => ix_al_reach P c' s2 n2) c s1 n1
  -> ix_al_reach P c s1 (min n1 (if s1 then S n2 else n2)).
induction 1.
+ (* Exhausted *)
  rewrite Nat.min_0_l.
  constructor.
+ (* Here *)
  assert (min n n2 <= n2) by apply Nat.le_min_r.
  revert H0; generalize (min n n2); intros n0 Hle.
  induction Hle.
  destruct s2;auto using al_reach_unstrict.
  auto using al_reach_pred.
+ (* Later *)
  assert (ix_al_reach P c s (S (min n n2))) as IH by (constructor;assumption).
  clear -IH.
  destruct s.
  assumption.
  pose proof (al_reach_pred IH).
  apply min_half_suc; assumption.
Qed.

Module AllPathSemantics <: ReachabilitySemantics.

(* Definitions *)
Definition index : Set := nat.
Definition ix_rel (i1 i2 : index) : Prop := (i1 = S i2).

Definition holds strict env (phi1 phi2 : formula cfg env) i :=
  forall rho gamma, phi1 rho gamma -> ix_al_reach (phi2 rho) gamma strict i.

(* Nontrivial proofs *)
(** Circularity **)
Lemma ix_rel_ind : forall env (phi phi' : formula cfg env),
      forall i0,
      (forall i, clos ix_rel false i0 i ->
                   (forall i', ix_rel i i' -> holds true phi phi' i') ->
                   holds true phi phi' i)
       -> holds true phi phi' i0.
intros.
apply nat_le_ind.
intros.
rewrite <- le_iff_clos_nat_pred in H0.
auto.
Qed.

Create HintDb holds_solve discriminated.
Hint Transparent holds : holds_solve.
Hint Unfold holds : holds_solve.

Hint Resolve al_here al_exhausted : holds_solve.
(* Hint Resolve al_reach_pred al_reach_unstrict : holds_solve. *)

Ltac holds_start := unfold index;intros;
  repeat match goal with
  | [|- holds _ _ _ _] => unfold holds;intros
  | [H : ix_rel ?l _ |- _] => unfold ix_rel in H;rewrite H in * |- *;clear H;clear l
  (* Use holds hypotheses *)
  | [H : holds _ ?phi _ _, Hphi : ?phi _ ?gamma |- _]=> specialize (H _ _ Hphi)
  | [H : forall _ _, ?phi _ _ -> _, Hphi : ?phi _ _ |- _] =>
    specialize (H _ _ Hphi)
  end.
(*
Ltac holds_start := intros;
  repeat match goal with
  (* open unnecessary uses of holds/indices *)
  | [i : index |- _] => destruct i
  | [H : holds _ _ _ (exist _ _ _) |- _] => unfold holds in H;simpl proj1_sig in H
  | [|- holds _ _ _ (exist _ _ _)] => unfold holds;simpl proj1_sig;unfold holds';intros
  | [H : ix_rel (exist _ _ _) _ |- _] => unfold ix_rel in H; simpl proj1_sig in H
  | [H : ix_rel _ (exist _ _ _) |- _] => unfold ix_rel in H; simpl proj1_sig in H
  (* Instantate a hypothesis quantified over ix_rel, as appears in strict trans *)
  | [H : forall i', ix_rel (exist _ ?x ?t) i' -> holds _ ?phi _ i',
       Hphi : ?phi _ ?x0 |- _ ] =>
    let Hprog := fresh "Hprog" in
    assert (clos S true x x0) as Hprog by clos_solve;
    let x1 := fresh "x1" with Hstep := fresh "Hstep" with Hreach := fresh "Hreach" in
    apply clos_true_step in Hprog; destruct Hprog as [x1 [Hstep Hreach]];
    specialize (H (exist _ x1 (terminates_next t _ Hstep)) Hstep)
  (* Use holds' hypotheses *)
  | [H : holds' _ ?phi _ ?x, Hphi : ?phi _ ?gamma |- _]=>
    let Hreach := fresh "Hreach" in
    assert (clos S false x gamma) as Hreach by clos_solve;
    specialize (H _ _ Hreach Hphi)
  | [H : exists _, clos S _ _ _ /\ _ |- _] => destruct H as [? []]
  end.
*)
Ltac holds_finish :=
  solve[auto with holds_solve
       |intuition
          (repeat match goal with
             | [H : forall _ _, ?phi _ _ -> _, Hphi : ?phi _ _ |- _] =>
               specialize (H _ _ Hphi)
           end;firstorder with holds_solve)
       ].
Ltac holds_finish' lem :=
  solve[eauto using lem with holds_solve
       |intuition
          (repeat match goal with
             | [H : forall _ _, ?phi _ _ -> _, Hphi : ?phi _ _ |- _] =>
               specialize (H _ _ Hphi)
           end;firstorder using lem with holds_solve)
       ].

Ltac holds_tac := holds_start;holds_finish.

(* Simple properties *)
Lemma holds_strict_later : forall env phi1 phi2 i,
                             @holds true env phi1 phi2 i ->
                             forall i', ix_rel i i' ->
                                        holds true phi1 phi2 i'.
holds_start. holds_finish' al_reach_pred.
Qed.

Lemma holds_unstrict : forall env phi1 phi2 i,
                         @holds true env phi1 phi2 i -> holds false phi1 phi2 i.
holds_start. holds_finish' al_reach_unstrict.
Qed.

Lemma holds_step : forall env (phi phi' : formula cfg env),
    (forall (e : env) (c : cfg),
      phi e c ->
      (exists c2 : cfg, SF c c2) /\ (forall c2 : cfg, SF c c2 -> phi' e c2)) ->
    forall i, holds true phi phi' i.
holds_start.
destruct H.
apply al_reach_pred;apply al_later;eauto with holds_solve.
Qed.

Lemma holds_refl : forall env phi i, @holds false env phi phi i.
holds_tac.
Qed.

Lemma holds_case :
    forall strict env (phi phi1 phi' : formula cfg env) i,
      holds strict phi phi' i -> holds strict phi1 phi' i ->
      holds strict (fun (e : env) (g : cfg) => phi e g \/ phi1 e g) phi' i.
holds_tac.
Qed.

Lemma holds_mut_conseq :
    forall strict env1 (phi1 phi2 : formula cfg env1)
                  env2 (phi1' phi2' : formula cfg env2),
     (forall gamma rho,
        phi1 rho gamma ->
        exists rho', phi1' rho' gamma /\
                     forall gamma', phi2' rho' gamma' -> phi2 rho gamma') ->
    forall i, holds strict phi1' phi2' i ->
              holds strict phi1 phi2 i.
holds_start;holds_finish' al_reach_impl.
Qed.

(** Transitivity **)
Lemma holds_trans : forall env phi phi' phi'' i,
    @holds false env phi phi' i ->
    holds false phi' phi'' i ->
    holds false phi phi'' i.
holds_start.
unfold holds in H0.
apply (al_reach_impl _ (H0 rho)) in H.
clear -H.
apply al_reach_join in H.
rewrite Nat.min_idempotent in H;assumption.
Qed.

Lemma holds_trans_strict : forall env phi phi' phi'' i,
    @holds true env phi phi' i ->
    (forall i' : index, ix_rel i i' -> holds false phi' phi'' i') ->
   holds true phi phi'' i.
holds_start.
destruct i.
constructor.
apply (al_reach_impl _ (H0 _ (eq_refl _) rho)) in H.
clear -H.
apply al_reach_join in H.
rewrite Nat.min_idempotent in H;assumption.
Qed.

Definition cfg := cfg.
Definition S := SF.

End AllPathSemantics.

Module AllPathSoundness := Soundness AllPathSemantics.

(* Now, define two versions of full soundness and show equivalences *)
(* We'll end up using some assumptions about decidability of
   stuckness and matching to show equivalence of tree- and path-based
   properties *)

Inductive closed_path (start : cfg) : Set :=
  | path_end : ~(exists c', SF start c') -> closed_path start
  | path_step : forall c', SF start c' -> closed_path c' -> closed_path start.
Fixpoint path_length c (path : closed_path c) : nat :=
  match path with
    | path_end _ => 0
    | path_step _ rest => 1 + path_length rest
  end.
Definition drop1 c (path : closed_path c) : {c' : cfg & closed_path c'} :=
  match path with
    | path_end final => existT _ c (path_end final)
    | @path_step _ c' _ rest => existT _ c' rest
  end.
Lemma drop_rebuild c (path : closed_path c) : path_length path <> 0 ->
   exists step : SF c (projT1 (drop1 path)), path = path_step step (projT2 (drop1 path)).
intro Hlen;destruct path;[exfalso|];eauto.
Qed.

Lemma drop_len c (path : closed_path c) :
  path_length (projT2 (drop1 path)) = pred (path_length path).
Proof.
destruct path;reflexivity.
Qed.

Inductive InPath c : forall c', closed_path c' -> Set :=
  | in_here : forall p, @InPath c c p
  | in_later : forall c' c'' (s : SF c' c'') (p' : closed_path c''),
                 InPath c p' -> InPath c (path_step s p').

Fixpoint tail_at c c' (path : closed_path c') (pf : InPath c path) : closed_path c :=
  match pf with
    | in_here p => p
    | in_later _ pf' => tail_at pf'
  end.

Lemma tail_len c c' (path : closed_path c') (pf : InPath c path) :
  path_length (tail_at pf) <= path_length path.
Proof.
induction pf;simpl;auto with arith.
Qed.

Inductive squash (A : Type) : Prop :=
  | inhabited : A -> squash A.

Definition StuckDecidable := forall c, (exists c', SF c c') \/ ~(exists c', SF c c').

Definition path_reach (P : cfg -> Prop) (c : cfg) : Prop :=
  forall (path : closed_path c), exists c', P c' /\ squash (InPath c' path).

Lemma path_reach_next P c c' : SF c c' -> ~ P c -> path_reach P c -> path_reach P c'.
intros Hstep Hnot_here Hpath.
unfold path_reach.
intro path.
specialize (Hpath (path_step Hstep path)).
destruct Hpath as [c0 [HPc0 Hpath']].
exists c0;split;[exact HPc0|].
destruct Hpath'.
remember (path_step Hstep path) as path' in H.
destruct H.
exfalso;auto.
inversion Heqpath'.
rewrite EqdepFacts.eq_sigT_sig_eq in H2.
destruct H2.
destruct x.
simpl in e.
subst p'.
constructor;assumption.
Qed.

Lemma path_reach_approx P (P_dec : forall c, P c \/ ~P c) (stuck_dec : StuckDecidable) :
  forall c, path_reach P c -> (forall n, ix_al_reach P c false n).
intros c H n. revert n c H. induction n; intros c H.
apply al_exhausted.
(* Need information about complete paths to proceed,
   if c is stuck we can't use later
 *)
destruct (stuck_dec c).
(* When the configuration isn't stuck, it could still be the case
   that some successors don't reach P, and path_reach P c holds
   only because P c is true now. *)
destruct (P_dec c);eauto using ix_al_reach, path_reach_next.
(* When the configuraton is stuck we can prove P holds here *)
+ specialize (H (path_end H0)).
  destruct H as [c' [Pc' Hhere]].
  replace c' with c in Pc'.
  apply al_here;assumption.
  destruct Hhere. inversion H. reflexivity.
Qed.

Lemma approx_path_reach P : forall c, (forall n, ix_al_reach P c false n) -> path_reach P c.
intros.
unfold path_reach.
intros.
specialize (H (S (path_length path))).
induction path.
simpl in H;inversion H;subst.
eauto using squash, InPath.
exfalso; firstorder.
inversion H;subst.
eauto using squash, InPath.
specialize (IHpath (H3 _ s));clear -IHpath;
firstorder using squash, InPath.
Qed.


(* Define unconditional versions of all-path reachability *)
CoInductive reach (P : cfg -> Prop) (c : cfg) : bool -> Prop :=
  | here : P c -> reach P c false
  | later : (exists c', SF c c') ->
               (forall c', SF c c' -> reach P c' false) ->
               forall s, reach P c s
.

Lemma reach_approx P c s : reach P c s -> forall n, ix_al_reach P c s n.
intros H n; revert s c H;induction n;intros s c H.
constructor.
inversion H;[apply al_here|apply al_later];auto.
Qed.

Lemma approx_defer P c : ~ P c ->
  (forall n, ix_al_reach P c false n) ->
  forall c', SF c c' -> (forall n, ix_al_reach P c' false n).
intros.
specialize (H0 (S n)).
inversion H0.
destruct (H H2).
auto.
Qed.

Lemma approx_reach P (P_dec : forall c, P c \/ ~ P c)
  (stuck_dec : StuckDecidable):
  forall c, (forall n, ix_al_reach P c false n) -> reach P c false.
cofix.
intros c Happrox.
destruct (stuck_dec c).
(* Later *)
destruct (P_dec c).
apply here; assumption.
apply later.
assumption.
intros.
apply approx_reach.
clear approx_reach.
apply approx_defer with c;assumption.
(* Here *)
clear approx_reach.
apply here.
specialize (Happrox 1).
inversion Happrox.
assumption.
destruct (H H1).
Qed.

Definition holds' env (phi1 phi2 : formula cfg env) strict :=
  forall rho gamma, phi1 rho gamma -> reach (phi2 rho) gamma strict.
Definition system_holds (A : system cfg) :=
  forall env (phi1 phi2 : formula cfg env),
    A env phi1 phi2 -> holds' phi1 phi2 true.

Theorem soundness : forall (A : system cfg) env (phi1 phi2 : formula cfg env),
                      (forall rho gamma, phi2 rho gamma \/ ~phi2 rho gamma) ->
                      StuckDecidable ->
                      IS cfg SF None A env phi1 phi2 ->
                      system_holds A ->
                      holds' phi1 phi2 false.
intros A env phi1 phi2 phi2_dec stuck_dec pf A_holds.
unfold holds'.
intros rho gamma Hphi1.
apply (approx_reach (phi2_dec rho) stuck_dec).
intro n.
revert rho gamma Hphi1.
fold (AllPathSemantics.holds false phi1 phi2 n).
apply (AllPathSoundness.soundness pf);trivial.
clear -A_holds.
unfold AllPathSoundness.system_holds.
intros.
specialize (A_holds _ _ _ H).
unfold AllPathSemantics.holds.
intros.
apply reach_approx.
auto.
Qed.