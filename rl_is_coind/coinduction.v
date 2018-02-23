(*
  This file contains the main soundness proof supporting our coinductive
  verification examples, by defining a semantics of claims,
  proving that it can be expressed as a greatest fixpoint,
  and then proving a soundness theorem giving a way to prove
  a set of claims are all true.

  In this file (used in most examples), 'reaches x P' holds
  if any execution path from configuration x is either infinite or
  reaches a configuration satisfying P.

  'reaches' is shown to be the greatest fixpoint of the 'step' function.

  'stable_sound' is plain coinduction theorem for 'reaches' and 'step',
  'proved_sound' is the generalized coinduction theorem also allowing
  the "proof" rules defined in 'trans'.
 *)
Set Contextual Implicit.
Set Implicit Arguments.

Section relations.
Variables (cfg : Type) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive reaches (k : cfg) (P : cfg -> Prop) : Prop :=
  (* reaches : Spec, but defining k and P as parameters
     gives a cleaner definition and induction principle. *)
| rdone : P k -> reaches k P
| rstep : forall k', cstep k k' -> reaches k' P -> reaches k P.

Definition sound (Rules : Spec) : Prop :=
  forall x P, Rules x P -> reaches x P.

Inductive step (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  (* step : Spec -> Spec *)
| sdone : P k -> step X k P
| sstep : forall k', cstep k k' -> X k' P -> step X k P.

Inductive next (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
| nstep : forall k', cstep k k' -> X k' P -> next X k P.

Lemma reaches_stable :
  (forall x P, reaches x P -> step reaches x P).
Proof. destruct 1;econstructor;eassumption. Qed.

CoFixpoint stable_sound (Rules : Spec)
  (Hstable : forall x P, Rules x P -> step Rules x P)
  : sound Rules :=
  fun x P H =>
  match Hstable _ _ H with
    | sdone pf => rdone pf
    | sstep Hstep H' =>
        rstep Hstep (stable_sound Hstable H')
  end.

(*
Inductive derived (X : Spec) k P : Prop :=
| dclaim : X k P -> derived X k P
| ddone : P k -> derived X k P
| dstep : forall k', cstep k k' -> derived X k' P -> derived X k P
| dtrans' : forall Q, derived X k Q -> (forall k', Q k' -> derived X k' P)
    -> derived X k P
| dproved : reaches k P -> derived X k P.
*)

Inductive trans (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  (* trans : Spec -> Spec *)
  | ddone : P k -> trans X k P
  | dtrans' : forall Q, trans X k Q -> (forall k', Q k' -> trans X k' P) -> trans X k P
  | drule : X k P -> trans X k P
  | dstep : forall k', cstep k k' -> trans X k' P -> trans X k P
  | dvalid : reaches k P -> trans X k P
  .
Definition dtrans_valid (X : Spec) (k : cfg) (P Q : cfg -> Prop)
  (rule : reaches k Q) (rest : forall k', Q k' -> trans X k' P) : trans X k P :=
  @dtrans' X k P Q (dvalid rule) rest.
Definition dtrans (X : Spec) (k : cfg) (P Q : cfg -> Prop)
  (rule : X k Q) (rest : forall k', Q k' -> trans X k' P) : trans X k P :=
  @dtrans' X k P Q (drule rule) rest.

Lemma trans_stable (Rules : Spec) :
  (forall x P, Rules x P -> step (trans Rules) x P)
  -> (forall x P, trans Rules x P -> step (trans Rules) x P).
induction 2;eauto using step.
destruct IHtrans; eauto using step, dtrans'.
destruct H0; eauto using step,dvalid.
Qed.

Lemma proved_sound (Rules : Spec) :
  (forall x P, Rules x P -> step (trans Rules) x P)
  -> sound Rules.
unfold sound.
intros H x P R.
eapply stable_sound.
apply trans_stable. eassumption.
apply drule. assumption.
Qed.

End relations.
