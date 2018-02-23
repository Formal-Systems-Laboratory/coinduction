Require Import generic_soundness.

Require Import reduction.

Require Import proofsystem.
Set Implicit Arguments.

Require Import Setoid.
Require Import Relation_Definitions.

Axiom cfg : Set.
Axiom S : cfg -> cfg -> Prop.

(* Showing one-path soundness.
  The final notion of one-path soundness considers a reachability rule
  satisfied if the initial configuration admits a diverging execution, so
  in the non-vacuous case we might as well assume the initial configuration
  terminates on all execution paths, and then this termination is itself
  a well-ordering we can use to justify circularity.
  (see "holds" for the unconditional definition)
 *)

(* Lemmas *)
Lemma clos_lift (A B : Type) (R1 : relation A) (R2 : relation B)
  (f : B -> A) :
  (forall x y, R1 x y -> forall x', x = f x' -> exists y', R2 x' y' /\ y = f y') ->
  forall strict x y,
  clos R1 strict x y ->
  forall x', x = f x' ->
  exists y', clos R2 strict x' y' /\ y = f y'.
induction 2;intros;
repeat match goal with
         | [H : _ -> _ -> ?R _ _ -> _, H1 : ?R _ _ |- _] => specialize (H _ _ H1)
         | [H : forall x, ?a = f x -> _, H1 : ?a = f _ |- _] => specialize (H _ H1)
         | [H : exists y', _ /\ _ = f y' |-_] =>
           destruct H as [? []]
       end;
eauto using clos.
Qed.

Lemma terminates_next : forall {A : Set} {R : relation A} (a : A),
  terminates a R -> forall b, R a b -> terminates b R.
destruct 1.
assumption.
Qed.

Lemma under_terminates : forall {A : Set} {R : relation A} (a : A),
  terminates a R -> forall (P : A -> Prop),
  (forall a0, clos R false a a0 ->
              (forall a', R a0 a' -> P a') ->
              P a0)
  -> P a.
intros A R a term P.
move term after P.
induction term as [a HAcc IH].
intro Hlater.
apply Hlater.
constructor.
intros a' Raa.
apply IH.
assumption.
intros a0 Ha'a0 Hnext.
apply Hlater.
clear -Raa Ha'a0. eauto using clos.
assumption.
Qed.

Lemma clos_cat'
     : forall (A : Type) (R : relation A) (a : A) (s1 : bool)
         (b : A) (s2 s3 : bool) (c : A),
       clos R s1 a b -> clos R s2 b c -> implb s3 (s1 || s2) = true -> clos R s3 a c.
intros.
pose proof (clos_cat H H0) as H2; clear -H1 H2.
destruct s3. simpl in H1; rewrite H1 in H2;assumption.
destruct (orb s1 s2);auto using clos_unstrict.
Qed.

Module ExReachability <: StateBasedReachability.

Definition cfg := cfg.
Definition S := S.

Definition index : Set := {gamma : cfg | terminates gamma S}.
Definition ix_rel (i1 i2 : index) : Prop :=
  S (proj1_sig i1) (proj1_sig i2).

Definition state_reaches strict (i : index) gamma P :=
  clos S false (proj1_sig i) gamma ->
  exists gamma', clos S strict gamma gamma' /\ P gamma'.

Definition holds strict env (phi phi' : formula cfg env) i :=
  forall rho gamma,
    phi rho gamma ->
    state_reaches strict i gamma (phi' rho).

(* Nontrivial proofs *)
(** Circularity **)
Lemma ix_rel_ind : forall env (phi phi' : formula cfg env),
      forall i0,
      (forall i, clos ix_rel false i0 i ->
                   (forall i', ix_rel i i' -> holds true phi phi' i') ->
                   holds true phi phi' i)
       -> holds true phi phi' i0.
unfold holds, state_reaches; intros env phi phi' i Hix_later.
destruct i as [a Hterm].
simpl.
apply (under_terminates Hterm).
intros a0 Haa0 Hnext.

assert (exists i', clos ix_rel false (exist _ a Hterm) i' /\ a0 = proj1_sig i').
  clear -Haa0. apply clos_lift with (R1:=S) (x:=a);[|assumption|reflexivity].
  intros.
  destruct x';simpl in *|- *;subst.
  assert (terminates y S) by (destruct t as [H0]; apply H0; assumption).
  exists (exist _ y H0). split;[|reflexivity].
  unfold ix_rel;simpl. assumption.
destruct H as [i' [Hreach Hend]].
specialize (Hix_later i' Hreach).
rewrite Hend.
apply Hix_later.
intros.
subst a0.
eauto.
Qed.

Ltac clear_except_path :=
repeat match goal with
  | [H : ?Hyp |- _] =>
    match Hyp with
      | terminates _ _ => fail 1
      | clos _ _ _ _ => fail 1
      | S ?x ?y => apply (clos_step _ true) in H
      | _ => clear H
    end
  end.
Ltac clos_solve :=
  clear_except_path;
match goal with
  | [|- clos _ false ?x ?x] => apply clos_refl
  | [|- clos _ false _ _] =>
    repeat match goal with
             | [H : clos _ true _ _ |- _] => apply clos_unstrict in H
           end;
    repeat match goal with
             | [H : clos ?S _ ?x ?y |- clos ?S _ ?x ?y ] => assumption
             | [H : clos ?S _ ?x ?y, H2 : clos ?S _ ?y _ |- clos ?S _ ?x _ ] =>
               pose proof (clos_trans H H2); clear H2
           end
  | [|- clos _ _ _ _] =>
    repeat match goal with
         | [H : clos ?S ?f ?x ?y |- clos ?S ?f ?x ?y ] => assumption
         | [H : clos ?S true ?x ?y, H2 : clos ?S _ ?y _ |- clos ?S _ ?x _ ] =>
           pose proof (clos_cons_lt H H2); clear H H2
         | [H : clos ?S _ ?x ?y, H2 : clos ?S true ?y _ |- clos ?S _ ?x _ ] =>
           pose proof (clos_cons_rt H H2); clear H H2
      end
end.

Hint Extern 0 (clos _ _ _ _) => clos_solve : holds_solve.

Ltac holds_start := intros;
  repeat match goal with
  (* open unnecessary uses of holds/indices *)
  | [i : index |- _] => destruct i
  | [H : ix_rel (exist _ _ _) _ |- _] => unfold ix_rel in H; simpl proj1_sig in H
  | [H : ix_rel _ (exist _ _ _) |- _] => unfold ix_rel in H; simpl proj1_sig in H
  | [H : state_reaches _ (exist _ _ _) _ _ |- _] =>
    unfold state_reaches in H;simpl proj1_sig in H
  | [|- state_reaches  _ (exist _ _ _) _ _] =>
    unfold state_reaches;simpl proj1_sig;intros
  (* Use hypotheses *)
  | [H : (clos S ?f ?x ?y) -> _ |- _] =>
    match goal with
      | [H' : clos S f x y |- _] =>
        specialize (H H')
      | _ =>
        let Hpath := fresh "Hpath" in
        assert (clos S f x y) as Hpath by clos_solve;
          specialize (H Hpath)
    end
  (* Open results *)
  | [H : exists gamma : _, _ |- _] =>
    destruct H
  | [H : _ /\ _ |- _] =>
    destruct H
  end.

Lemma reach_later : forall i i', ix_rel i i' ->
    forall gamma P,
      state_reaches true i gamma P ->
      state_reaches true i' gamma P.
  Proof.
    holds_start; eauto with holds_solve.
  Qed.
  Lemma reach_unstrict : forall i gamma P,
    state_reaches true i gamma P -> state_reaches false i gamma P.
  Proof.
    holds_start; eauto with holds_solve.
  Qed.

  Lemma reach_refl : forall i gamma (P : cfg -> Prop),
                           P gamma -> state_reaches false i gamma P.
  Proof.
    holds_start; firstorder with holds_solve.
  Qed.

  Lemma reach_step : forall i gamma (P : cfg -> Prop),
    (exists gamma', S gamma gamma') ->
    (forall gamma', S gamma gamma' -> P gamma') ->
      state_reaches true i gamma P.
  Proof.
    holds_start; eauto with holds_solve.
  Qed.

  Lemma reach_impl : forall (P Q : cfg -> Prop),
                           (forall c, P c -> Q c) ->
                           forall strict i gamma,
                             state_reaches strict i gamma P ->
                             state_reaches strict i gamma Q.
  Proof.
    holds_start; eauto with holds_solve.
  Qed.

  Lemma reach_join : forall i gamma P,
    state_reaches false i gamma
     (fun gamma' => state_reaches false i gamma' P) ->
    state_reaches false i gamma P.
  Proof.
    holds_start;eauto with holds_solve.
  Qed.

  Lemma reach_join_strict : forall i gamma P,
    state_reaches true i gamma
     (fun gamma' => forall i', ix_rel i i' -> state_reaches false i' gamma' P) ->
    state_reaches true i gamma P.
  Proof.
    holds_start.
    unfold ix_rel in H1; simpl proj1_sig in H1.
    assert (clos S true x x0) by clos_solve;clear H0.
    destruct (clos_true_step H2) as [x' [Hxx' Hx'x0]].
    specialize (H1 (exist _ x' (terminates_next t _ Hxx')) Hxx' Hx'x0).
    firstorder with holds_solve.
  Qed.

End ExReachability.

Module ExPathSemantics := StateBasedSemantics ExReachability.
Module ExPathSoundness := Soundness ExPathSemantics.

Definition holds cfg S strict env (phi phi' : formula cfg env) :=
  forall rho gamma, terminates gamma S ->
    phi rho gamma -> exists gamma', phi' rho gamma' /\ clos S strict gamma gamma'.

Lemma approx_holds env (phi phi' : formula cfg env) strict :
  (forall i, ExPathSemantics.holds strict phi phi' i) ->
  holds S strict phi phi'.
intro H. unfold holds.
intros.
specialize (H (exist _ gamma H0) _ _ H1 (clos_refl _ _)).
firstorder.
Qed.

Lemma holds_approx env (phi phi' : formula cfg env) strict :
  holds S strict phi phi' ->
  (forall i, ExPathSemantics.holds strict phi phi' i).
intros Hstrong i.
destruct i as [gamma term].
unfold ExPathSemantics.holds, ExReachability.holds.
intros rho gamma1 Hphi Hreach.
specialize (Hstrong _ gamma1 (terminates_fwd term Hreach) Hphi).
firstorder.
Qed.

Definition system_holds cfg S (A : system cfg) :=
  forall env phi1 phi2, @A env phi1 phi2 -> holds S true phi1 phi2.

Theorem soundness (A : system cfg) env (phi1 phi2 : formula cfg env) :
  IS cfg S None A env phi1 phi2 ->
  system_holds S A ->
  holds S false phi1 phi2.
Proof.
intros pf HA.
apply approx_holds.
intro i.
apply (ExPathSoundness.soundness pf);trivial.
clear -HA i.
pose proof holds_approx.
unfold ExPathSoundness.system_holds;intros.
eauto.
Qed.

(* Print Assumptions soundness. *)