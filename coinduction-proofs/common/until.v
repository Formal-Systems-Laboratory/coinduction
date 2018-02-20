Set Implicit Arguments.

Section relations.
Variables (cfg : Set) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> cfg -> Prop) -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive until (k : cfg) (T : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | rdone : P k -> until k T P
  | rstep : forall k', cstep k k' -> T k k' -> until k' T P -> until k T P.

Definition sound (Rules : Spec) : Prop :=
  forall x T P, Rules x T P -> until x T P.

Inductive step (X : Spec) (k : cfg) (T : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step X k T P
  | sstep : forall k', cstep k k' -> T k k' -> X k' T P -> step X k T P
  .

CoFixpoint stable_sound (Rules : Spec)
  (Hstable : forall x T P, Rules x T P -> step Rules x T P)
  : sound Rules := fun x T P H => match Hstable _ _ _ H with
    | sdone pf => rdone _ _ _ pf
    | sstep k' Hstep step_ok H' => rstep Hstep step_ok (stable_sound Hstable _ _ _ H')
end.

Lemma until_gfp : forall x T P, step until x T P <-> until x T P.
Proof. split;destruct 1;econstructor(eassumption). Qed.

Inductive trans (X : Spec) (k : cfg) (T : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | drule : X k T P -> trans X k T P
  | ddone : P k -> trans X k T P
  | dstep : forall k', cstep k k' -> T k k' -> trans X k' T P -> trans X k T P
  | dstrong : forall (T' : cfg -> cfg -> Prop),
       (forall a b, T' a b -> T a b) -> trans X k T' P -> trans X k T P
  | dtrans' : forall Q, trans X k T Q -> (forall k', Q k' -> trans X k' T P) -> trans X k T P
  .

Lemma absorb_step : forall X k T P, step (trans X) k T P -> trans X k T P.
Proof. destruct 1;eauto using trans. Qed.

Lemma trans_ok : forall X k T P, trans (step X) k T P -> step (trans X) k T P.
induction 1;try match goal with [H : step _ _ _ _ |- _] => destruct H end;
            try solve[eauto using step, trans, absorb_step].
Qed.

Lemma trans_stable (Rules : Spec) :
  (forall x T P, Rules x T P -> step (trans Rules) x T P)
  -> (forall x T P, trans Rules x T P -> step (trans Rules) x T P).
induction 2;eauto using step;
destruct IHtrans; eauto using step, trans.
Qed.

Lemma proved_sound (Rules : Spec) :
  (forall x T P, Rules x T P -> step (trans Rules) x T P)
  -> sound Rules.
unfold sound.
intros.
apply stable_sound with (trans Rules).
apply trans_stable. assumption.
apply drule. assumption.
Qed.

End relations.
