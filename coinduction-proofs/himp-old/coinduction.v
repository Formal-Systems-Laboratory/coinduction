Set Implicit Arguments.

Require Import domains.
Require Import kstyle.

CoInductive reaches (x : kcfg) (P : kcfg -> Prop) : Prop :=
  | done : P x -> reaches x P
  | step : forall y, kstep x y -> reaches y P -> reaches x P
  .

Definition steps x y := reaches x (kequiv y).

Definition RRel : Type := kcfg -> (kcfg -> Prop) -> Prop.
Definition subrel (kcfg B : RRel) : Prop := forall x P, kcfg x P -> B x P.

Definition sound (X : RRel) : Prop := subrel X reaches.

(* Base functor of the path predicate *)
Inductive stepF (X : RRel) (x : kcfg) (P : kcfg -> Prop) : Prop :=
  | DoneF : P x -> stepF X x P
  | StepF : forall y, kstep x y -> X y P -> stepF X x P.

Definition stable (X : RRel) : Prop := subrel X (stepF X).

CoFixpoint stable_sound X (Hstable : stable X) : sound X :=
  fun x P HxP =>
  match Hstable _ _ HxP with
  | DoneF Px => done _ _ Px
  | StepF y Rxy XyP => step Rxy (@stable_sound _ Hstable _ _ XyP)
  end.

Definition F_stable (F : RRel -> RRel) (X : RRel) : Prop := subrel X (stepF (F X)).

(* Focused version of transitivity,
   assuming we only want to apply transitivity
   on assumed circularities. *)
Inductive trans (X : RRel) (x : kcfg) (P : kcfg -> Prop) : Prop :=
  | tdone : P x -> trans X x P
  | tstep : forall y, kstep x y -> trans X y P -> trans X x P
  | tcirc : forall Q, X x Q -> (forall t, Q t -> trans X t P) -> trans X x P
  .

Lemma ttrans : forall X x P Q,
   trans X x Q -> (forall t, Q t -> trans X t P) -> trans X x P.
Proof.
induction 1;eauto using trans.
Qed.

Lemma step_mono : forall (X : RRel) x (P Q : kcfg -> Prop),
   (forall x, P x -> stepF X x Q) ->
   (forall x, X x P -> X x Q) ->
   stepF X x P -> stepF X x Q.
destruct 3;eauto using stepF.
Qed.

Lemma trans_derived (X : RRel) (trans_stable : F_stable trans X) : stable (trans X).
induction 1;eauto using stepF,step_mono,ttrans.
Qed.

Definition trans_sound (X : RRel) (trans_stable : F_stable trans X) : sound X.
intros x P HxP; apply (@stable_sound (trans X)).
exact (trans_derived trans_stable).
eauto using trans.
Qed.

(* some tactics for execution *)
