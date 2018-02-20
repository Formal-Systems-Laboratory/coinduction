(*
  This file generalizes 'all_proof.v' further by
  adding an invariant to the claim language,
  with a similar interpretation to the "Guarantee" part
  of a Rely-Guarantee claim.

  In the specification 'until x T P', the invariant 'T'
  is a relation on configurations, 'cfg -> cfg -> Prop'
  rather than a unary predicate like 'P : T'.

  In this file, a specification only holds if in every complete
  path from x, all the steps before reaching any configuration in P
  are also included in T, in addition to no such paths getting stuck
  without reaching a state in P.
 *)

Set Implicit Arguments.

Section relations.
Variables (cfg : Set) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> cfg -> Prop) -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive until (k : cfg) (T : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | rdone : P k -> until k T P
  | rstep : (exists k', cstep k k') -> (forall k', cstep k k' -> T k k' /\ until k' T P) -> until k T P.

Definition sound (Rules : Spec) : Prop :=
  forall x T P, Rules x T P -> until x T P.

Inductive step (X : Spec) (k : cfg) (T : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step X k T P
  | sstep : (exists k', cstep k k') -> (forall k', cstep k k' -> T k k' /\ X k' T P) -> step X k T P
.

CoFixpoint stable_sound (Rules : Spec)
  (Hstable : forall x T P, Rules x T P -> step Rules x T P)
  : sound Rules := fun x T P H =>
match Hstable _ _ _ H with
    | sdone pf => rdone _ _ _ pf
    | sstep not_stuck Hsteps => rstep not_stuck (fun k' Hstep =>
        let (Hpres, Hk') := Hsteps k' Hstep
        in conj Hpres (stable_sound Hstable k' T P Hk'))
end.

Inductive trans (X : Spec) (k : cfg) (T : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | drule : X k T P -> trans X k T P
  | ddone : P k -> trans X k T P
  | dstep' : (exists k', cstep k k') ->
             (forall k', cstep k k' -> T k k') ->
             (forall k', cstep k k' -> trans X k' T P) (* split into two functions to get a better induction principle *)
             -> trans X k T P
  | dstrong : forall (T' : cfg -> cfg -> Prop),
       (forall a b, T' a b -> T a b) -> trans X k T' P -> trans X k T P
  | dtrans' : forall Q, trans X k T Q -> (forall k', Q k' -> trans X k' T P) -> trans X k T P
  .

Lemma absorb_step : forall X k T P, step (trans X) k T P -> trans X k T P.
Proof. destruct 1;constructor(solve[firstorder]). Qed.

Lemma absorb_step_inner : forall X k T P, trans (step X) k T P -> trans X k T P.
Proof. induction 1;eauto using trans.
  destruct H;constructor(solve[firstorder using drule]).
Qed.

Lemma trans_ok : forall X k T P, trans (step X) k T P -> step (trans X) k T P.
induction 1;try match goal with [H : step _ _ _ _ |- _] => destruct H end;eauto using step;
firstorder eauto using trans, absorb_step_inner.
Qed.

Lemma trans_stable (Rules : Spec) :
  (forall x T P, Rules x T P -> step (trans Rules) x T P)
  -> (forall x T P, trans Rules x T P -> step (trans Rules) x T P).
induction 2;eauto using step;
destruct IHtrans; firstorder eauto using step, trans.
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
