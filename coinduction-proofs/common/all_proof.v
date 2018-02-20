(*
 This file is parallel to proof.v, but starts
 with a definition of claims where 'reaches x P'
 holds when every maximal path from x is either
 infinite or reaches a configuration satisfying P.
 In other words, no path from x reaches a stuck
 configuration without also encountering a state in P.

 This is shown to be the greatest fixpoint of
 a suitably-modified 'step', and a version of
 'prove_sound' is proved for this relation.

 This interpretation of claims is more suitable for
 nondeterministic languages.
 *)

Set Implicit Arguments.

Section relations.
Variables (cfg : Set) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive reaches (k : cfg) (P : cfg -> Prop) : Prop :=
  | rdone : P k -> reaches k P
  | rstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> reaches k' P) -> reaches k P.

Definition sound (Rules : Spec) : Prop :=
  forall x P, Rules x P -> reaches x P.

Inductive step (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step X k P
  | sstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> X k' P) -> step X k P
  .

Lemma sound_stable : forall x P, reaches x P -> step reaches x P.
Proof. destruct 1;constructor(assumption). Qed.

CoFixpoint stable_sound (Rules : Spec)
  (Hstable : forall x P, Rules x P -> step Rules x P)
  : sound Rules := fun x P H => match Hstable _ _ H with
    | sdone pf => rdone _ _ pf
    | sstep prog pres => rstep prog
       (fun k' Hstep => stable_sound Hstable k' _ (pres k' Hstep))
  end.

Inductive trans (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  | ddone : P k -> trans X k P
  | dtrans : forall Q, X k Q -> (forall k', Q k' -> trans X k' P) -> trans X k P
  | dstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> trans X k' P) -> trans X k P
  .

Lemma trans_trans (X : Spec) :
  forall x P Q,
    trans X x P -> (forall y, P y -> trans X y Q) -> trans X x Q.
induction 1;eauto using trans.
Qed.

Lemma trans_stable (Rules : Spec) :
  (forall x P, Rules x P -> step (trans Rules) x P)
  -> forall x P, trans Rules x P -> step (trans Rules) x P.
induction 2;try econstructor(eassumption).
destruct (H _ _ H0);eauto using step,trans_trans.
Qed.

Lemma proved_sound (Rules : Spec) :
  (forall x P, Rules x P -> step (trans Rules) x P)
  -> sound Rules.
unfold sound.
intros.
apply stable_sound with (trans Rules);
eauto using trans, trans_stable.
Qed.

End relations.
