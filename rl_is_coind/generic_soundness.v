Require Import Wellfounded.
Require Import reduction.

Require Import proofsystem.
Set Implicit Arguments.

(* A generic soundness proof.
   The proof is parameterized over a semantic interpretation of reachability rules,
   which can be instantiated to show one-path or all-path soundness.

   The semantics of a rule must be further parameterized by some kind of "index"
   with a well-founded approximation order, used to justifying circularity.

   This module reduces showing soundess of the proof system to showing a few
   lemmas about the selected semantics of reachability rules.

   The soundness result proved in this module shows that the conclusion of
   the proof holds with any index. To finish a specific soundness proof this
   should be shown equaivalent to some un-indexed notion of soundenss.
 *)

Lemma clos_true_step : forall {A: Set} (R : A -> A -> Prop) x z, clos R true x z ->
                                   exists y, R x y /\ clos R false y z.
intros.
rewrite clos_iff_left in H;inversion H;subst;rewrite <- ?clos_iff_left in * |-;
eauto using clos_refl, clos_unstrict.
Qed.

Module Type ReachabilitySemantics.
  Parameter cfg : Set.
  Parameter S : cfg -> cfg -> Prop.

  Parameter index : Set.
  (* This is one step of soundness relation *)
  Parameter ix_rel : index -> index -> Prop.

  Parameter holds : bool -> forall env, 
                      formula cfg env -> formula cfg env->
                      index -> Prop.

  (*
  Parameter ix_wf : well_founded (fun x y => ix_rel y x).
   *)

  (* Will this lemma be any harder to supply than one that
     distinguishes a one-step and all-step version of ix_rel,
     and only promises immediate successors in the
     argument of the hypothesis? *)
  Parameter ix_rel_ind : forall env (phi phi' : formula cfg env),
      forall i0,
      (forall i, clos ix_rel false i0 i ->
                   (forall i', ix_rel i i' -> holds true phi phi' i') ->
                   holds true phi phi' i)
       -> holds true phi phi' i0.

  Parameter holds_strict_later : forall env phi1 phi2 i,
                                   @holds true env phi1 phi2 i ->
                                   forall i', ix_rel i i' ->
                                   holds true phi1 phi2 i'.

  Parameter holds_unstrict : forall env phi1 phi2 i,
                           @holds true env phi1 phi2 i -> holds false phi1 phi2 i.


  Parameter holds_step : forall env (phi phi' : formula cfg env),
    (forall (e : env) (c : cfg),
      phi e c ->
      (exists c2 : cfg, S c c2) /\ (forall c2 : cfg, S c c2 -> phi' e c2)) ->
    forall i, holds true phi phi' i.
  Parameter holds_refl : forall env phi i, @holds false env phi phi i.

  Parameter holds_trans_strict : forall env phi phi' phi'' i,
    @holds true env phi phi' i ->
    (forall i' : index, ix_rel i i' -> holds false phi' phi'' i') ->
   holds true phi phi'' i.
  Parameter holds_trans : forall env phi phi' phi'' i,
    @holds false env phi phi' i ->
    holds false phi' phi'' i ->
    holds false phi phi'' i.

  Parameter holds_case :
    forall strict env (phi phi1 phi' : formula cfg env) i,
      holds strict phi phi' i -> holds strict phi1 phi' i ->
      holds strict (fun (e : env) (g : cfg) => phi e g \/ phi1 e g) phi' i.

  Parameter holds_mut_conseq :
    forall strict env1 (phi1 phi2 : formula cfg env1)
                  env2 (phi1' phi2' : formula cfg env2),
     (forall gamma rho,
        phi1 rho gamma ->
        exists rho', phi1' rho' gamma /\
                     forall gamma', phi2' rho' gamma' -> phi2 rho gamma') ->
    forall i, holds strict phi1' phi2' i ->
              holds strict phi1 phi2 i.

End ReachabilitySemantics.

Module Type StateBasedReachability.
  Parameter cfg : Set.
  Parameter S : cfg -> cfg -> Prop.

  Parameter index : Set.
  (* This is one step of soundness relation *)
  Parameter ix_rel : index -> index -> Prop.

  Parameter state_reaches : bool -> index -> cfg -> (cfg -> Prop) -> Prop.

  Definition holds strict env (phi phi' : formula cfg env) i :=
    forall rho gamma,
      phi rho gamma ->
      state_reaches strict i gamma (phi' rho).

  Parameter ix_rel_ind : forall env (phi phi' : formula cfg env),
      forall i0,
      (forall i, clos ix_rel false i0 i ->
                   (forall i', ix_rel i i' -> holds true phi phi' i') ->
                   holds true phi phi' i)
       -> holds true phi phi' i0.

  Parameter reach_later : forall i i', ix_rel i i' ->
    forall gamma P,
      state_reaches true i gamma P ->
      state_reaches true i' gamma P.

  Parameter reach_unstrict : forall i gamma P,
    state_reaches true i gamma P -> state_reaches false i gamma P.

  (* These are really from axiom cases, maybe make it generic *)
  Parameter reach_refl : forall i gamma (P : cfg -> Prop),
                           P gamma -> state_reaches false i gamma P.
  Parameter reach_step : forall i gamma (P : cfg -> Prop),
    (exists gamma', S gamma gamma') ->
    (forall gamma', S gamma gamma' -> P gamma') ->
      state_reaches true i gamma P.

  Parameter reach_impl : forall (P Q : cfg -> Prop),
                           (forall c, P c -> Q c) ->
                           forall strict i gamma,
                             state_reaches strict i gamma P ->
                             state_reaches strict i gamma Q.

  Parameter reach_join : forall i gamma P,
    state_reaches false i gamma
     (fun gamma' => state_reaches false i gamma' P) ->
    state_reaches false i gamma P.
  Parameter reach_join_strict : forall i gamma P,
    state_reaches true i gamma
     (fun gamma' => forall i', ix_rel i i' -> state_reaches false i' gamma' P) ->
    state_reaches true i gamma P.

End StateBasedReachability.

Module StateBasedSemantics (Reach : StateBasedReachability)
  <: ReachabilitySemantics.

  Import Reach.

  Definition cfg := cfg.
  Definition S := S.
  Definition index := index.
  Definition ix_rel := ix_rel.
  Definition holds := holds.
  Definition ix_rel_ind := ix_rel_ind.

  Lemma holds_strict_later : forall env phi1 phi2 i,
                                   @holds true env phi1 phi2 i ->
                                   forall i', ix_rel i i' ->
                                   holds true phi1 phi2 i'.
    unfold holds, Reach.holds; eauto using reach_later.
  Qed.

  Lemma holds_unstrict : forall env phi1 phi2 i,
                           @holds true env phi1 phi2 i ->
                           @holds false env phi1 phi2 i.
    unfold holds, Reach.holds; eauto using reach_unstrict.
  Qed.

  Lemma holds_step : forall env (phi phi' : formula cfg env),
    (forall (e : env) (c : cfg),
      phi e c ->
      (exists c2 : cfg, S c c2) /\ (forall c2 : cfg, S c c2 -> phi' e c2)) ->
    forall i, holds true phi phi' i.
    unfold holds, Reach.holds; intros; apply reach_step;firstorder.
  Qed.

  Lemma holds_refl : forall env phi i, @holds false env phi phi i.
    unfold holds, Reach.holds; intros; apply reach_refl;assumption.
  Qed.

  Lemma holds_case :
    forall strict env (phi phi1 phi' : formula cfg env) i,
      holds strict phi phi' i -> holds strict phi1 phi' i ->
      holds strict (fun (e : env) (g : cfg) => phi e g \/ phi1 e g) phi' i.
  Proof.
    firstorder.
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
  Proof.
    unfold holds, Reach.holds;intros.
    specialize (H _ _ H1).
    firstorder using reach_impl.
  Qed.

  Lemma holds_trans : forall env phi phi' phi'' i,
    @holds false env phi phi' i ->
    holds false phi' phi'' i ->
    holds false phi phi'' i.
  Proof.
    unfold holds, Reach.holds;intros.
    eauto using reach_join, reach_impl.
  Qed.

  Lemma holds_trans_strict : forall env phi phi' phi'' i,
    @holds true env phi phi' i ->
    (forall i' : index, ix_rel i i' -> holds false phi' phi'' i') ->
   holds true phi phi'' i.
  Proof.
    unfold holds, Reach.holds;intros.
    eauto using reach_join_strict, reach_impl.
  Qed.
End StateBasedSemantics.

Module Soundness(Sem : ReachabilitySemantics).  
  Import Sem.

  Definition system_holds (S : system cfg) (i : index) : Prop :=
    forall env phi1 phi2, S env phi1 phi2 -> holds true phi1 phi2 i.

  Lemma system_next (S : system cfg) (i : index) :
    system_holds S i -> forall i', ix_rel i i' -> system_holds S i'.
  Proof. unfold system_holds; eauto using holds_strict_later. Qed.

  Lemma system_later (S : system cfg) (i : index) :
    system_holds S i -> forall i', clos ix_rel false i i' -> system_holds S i'.
  Proof. intros Hsys i' Hpath; revert Hsys; induction Hpath; eauto using system_next. Qed.
 
  Lemma holds_weak : forall (C : option (system cfg)) env phi1 phi2 i,
                       @holds true env phi1 phi2 i ->
                       holds
                       (match C with
                         | None => false
                         | Some _ => true
                       end) phi1 phi2 i.
  Proof.
    destruct C;auto using holds_unstrict.
  Qed.

  Lemma holds_conseq : forall strict env (phi1 phi2 phi1' phi2' : formula cfg env),
    forall env (phi1 phi2 phi1' phi2' : formula cfg env),
    (forall rho gamma, phi1 rho gamma -> phi1' rho gamma) ->
    (forall rho gamma, phi2' rho gamma -> phi2 rho gamma) ->
    forall i, holds strict phi1' phi2' i ->
              holds strict phi1 phi2 i.
    intros.
    revert H1.
    apply holds_mut_conseq.
    firstorder.
  Qed.

    Ltac spec_ih :=
    let HA := fresh "HA" in
    let HC := fresh "HC" in
    intros ? HA HC;
    match goal with
      | [IHcirc : appcontext C [cons_opt_system] |-_] => idtac
      | _ => repeat match goal with
                        [IH : forall i, system_holds _ i -> _ |- _] =>
                        specialize (IH _ HA HC)
                    end
    end.

  Lemma soundness : forall C A env phi1 phi2,
                      IS cfg S C A env phi1 phi2 ->
                      forall (i : index),
                        system_holds A i ->
                        match C with
                          | None => True
                          | Some S' => forall i', ix_rel i i' -> system_holds S' i'
                        end ->
                        holds (
                        match C with
                          | None => false
                          | Some _ => true
                        end) phi1 phi2 i.
  Proof.
  induction 1;spec_ih.
  + (* step *)
    auto using holds_weak, holds_step.
  + (* axiom *)
    auto using holds_weak.
  + (* refl *)
    destruct C;[destruct H|]; auto using holds_refl.
  + (* trans *)
    destruct C.
    * assert (forall i', ix_rel i i' -> holds false phi' phi'' i') as IH2.
        clear -IHIS2 HA HC.
        intros. apply IHIS2;[clear IHIS2|exact I].
        assert (system_holds A i') by (eauto using system_next).
        firstorder.
      clear -IHIS1 IH2.
      eauto using holds_trans_strict.
    * assert (holds false phi' phi'' i) as IH2 by (clear -IHIS2 HA HC; auto).
      clear -IHIS1 IH2.
      eauto using holds_trans.
  + (* consequence *)
    eauto using holds_conseq.
  + (* case *)
    auto using holds_case.
  + (* abstr *)
    revert IHIS;clear;apply holds_mut_conseq;firstorder.
  + (* abstr' *)
    revert IHIS; clear -H; apply holds_mut_conseq.
    firstorder;eexists;split;[eassumption|];instantiate;firstorder.
  + (* circularity *)
    apply holds_weak.
    apply ix_rel_ind.
    intros i0 Hii0 IHlater.
    apply IHIS; clear H IHIS.
    eauto using system_later.
    simpl.
    intros i' Hi'.
    unfold system_holds.
    intros rho phi1 phi2 H.
    destruct H.
    * (* rules from C *)
      destruct C;[|solve[destruct H]].
      simpl in H.
      assert (forall i', clos ix_rel true i i' -> system_holds s i').
        clear -HC. intros.
        apply clos_true_step in H.
        destruct H as [i1 [Hstep Hrest]].
        eauto using system_later.
      clear HC; rename H0 into HC.
      assert (clos ix_rel true i i').
        clear -Hi' Hii0.
        eauto using clos, clos_cons_rt.
      specialize (HC _ H0).
      auto.
    * (* The added rule *)
      destruct H as [-> [-> ->]].
      unfold eq_rect_r in * |- *; simpl eq_rect in * |- *.
      auto.
  + (* subst *)
    eauto using holds_mut_conseq.
  + (* Logical framing *)
    revert IHIS;
    eapply holds_mut_conseq;
    intuition;
    eauto.
  Qed.
End Soundness.
