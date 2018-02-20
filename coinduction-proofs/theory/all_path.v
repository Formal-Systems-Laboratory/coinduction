Set Implicit Arguments.

Create HintDb mono discriminated.

Section ExPath.

Variable cfg : Set.
Variable step : cfg -> cfg -> Prop.

(* The actual semantic notion of reachability *)
CoInductive reaches (x : cfg) (P : cfg -> Prop) : Prop :=
  | Done : P x -> reaches x P
  | Step : (exists y, step x y) ->
           (forall y, step x y -> reaches y P) -> reaches x P
  .

Definition RRel : Type := cfg -> (cfg -> Prop) -> Prop.
Definition subrel (A B : RRel) : Prop := forall x P, A x P -> B x P.
Lemma subrel_trans (A B C : RRel) : subrel A B -> subrel B C -> subrel A C.
Proof. firstorder. Qed.

(* A set of claimed proerties is sound if all are valid *)
Definition sound (X : RRel) : Prop := subrel X reaches.

(* To prove soundness, we will use coinduction *)
(* First, here is a functor of which reaches is the greatest fixpoint *)
Inductive stepF (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | DoneF : P x -> stepF X x P
  | StepF : (exists y, step x y) ->
            (forall y, step x y -> X y P) -> stepF X x P.
(* To show it's actually a functor, we need to prove monotonicity. *)

Definition mono (F : RRel -> RRel) := forall A B, subrel A B -> subrel (F A) (F B).
Lemma step_mono : mono stepF.
(* For most simple types, we just need to do a case analysis, apply the
   hypothesis if applicable, and reapply some constructor, so name the tactic*)
Ltac mono_tac typename := induction 2;eauto using typename.
mono_tac stepF.
Qed.
Hint Resolve step_mono : mono.

(* Now that we have a functor, we'll show reaches is a fixpoint *)
Lemma reaches_fixed : forall x P, reaches x P <-> stepF reaches x P.
split;destruct 1;eauto using stepF,reaches.
Qed.

(* One equivalent definition of being the greatest fixpoint of
   F is that a fixpoint includes every F-stable set *)

(* A set of claims is stable if each is also justified by
   stepF from other claims in the set *)
Definition stable (X : RRel) : Prop := subrel X (stepF X).

CoFixpoint stable_sound X (Hstable : stable X) : sound X.
intros x P HxP.
apply Hstable in HxP. destruct HxP.
apply Done;assumption. 
apply Step. assumption.
   intros y Hstep.
    unfold sound,subrel in stable_sound.
    apply (stable_sound _ Hstable).
    clear stable_sound. auto.
Qed.        

Inductive trans (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
| Trans : forall Q, X x Q -> (forall t, Q t -> X t P) -> trans X x P.

Lemma trans_mono : mono trans.
firstorder.
Qed.

Inductive derivedF (F : RRel -> RRel)
                   (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dleaf : X x P -> derivedF F X x P
  | dstep : stepF (derivedF F X) x P -> derivedF F X x P
  | drule' : forall (Q : RRel), subrel Q (derivedF F X) ->
                                F Q x P -> derivedF F X x P.
Definition drule F X x P : F (derivedF F X) x P -> derivedF F X x P :=
  drule' _ _ (fun _ _ H => H).

Definition union (F G : RRel -> RRel) : RRel -> RRel :=
  fun X x P => F X x P \/ G X x P.
Lemma union_mono F G : mono F -> mono G -> mono (union F G).
firstorder.
Qed.

Definition comp_valid (F : RRel -> RRel) : Prop :=
  forall X, subrel (F (stepF X)) (stepF (derivedF F X)).

(* This makes it clear it doesn't matter what other rules
   are used, X could be of the form derivedF (F + G') B,
   and by unioning it reduces to this
 *)

Lemma trans_valid : comp_valid trans.
unfold comp_valid.
destruct 1.
destruct H.
specialize (H0 _ H).
revert H0. apply step_mono. unfold subrel; auto using dleaf.
apply StepF.
assumption.
intros y Hstep.
specialize (H1 y Hstep).
apply drule.
eapply Trans.
apply dleaf.
eassumption.
intros t Qt.
specialize (H0 t Qt).
clear -H0.
apply dstep.
revert H0.
apply step_mono.
clear.
unfold subrel;auto using dleaf.
Qed.

End ExPath.
