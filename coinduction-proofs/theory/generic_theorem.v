(* Prove the fully generic main theorem, Lemma main,
   and show that it implies the form used in proofs,
   proved_sound in /common/proofs.v *)

Require Import Classes.Morphisms.

Section Lattice.
Variable A : Type.

Definition mono (F : (A -> Prop) -> (A -> Prop)) :=
  forall (X Y : A -> Prop),
   (forall a, X a -> Y a) ->
   (forall a, F X a -> F Y a).

Definition fixpoint (F : (A -> Prop) -> (A -> Prop)) (X : A -> Prop) :=
  forall a, X a <-> F X a.

Inductive lfp F : forall (m : mono F) (a : A), Prop :=
  | lfp_roll : forall m (Q : A -> Prop) , (forall a, Q a -> lfp F m a) ->
      forall a, F Q a -> lfp F m a.

Lemma lfp_fixes : forall F m, fixpoint F (lfp F m).
split. destruct 1. apply (m _ _ H). assumption.
intro. apply lfp_roll with (lfp F m). trivial. assumption.
Qed.

Lemma lfp_least : forall F m X, fixpoint F X ->
  (forall a, lfp F m a -> X a).
intros.
induction H0. apply m in H1. apply H1 in H2. apply H in H2. assumption.
Qed.

Lemma lfp_induction : forall X F (m : mono F),
  (forall a, F X a -> X a) ->
  (forall a, lfp F m a -> X a).
intros. induction H0. apply H. revert H2. apply m. assumption.
Qed.

CoInductive gfp F : forall (m : mono F) (a : A), Prop :=
  | gfp_roll : forall m (Q : A -> Prop) , (forall a, Q a -> gfp F m a) ->
      forall a, F Q a -> gfp F m a.

Lemma gfp_fixes : forall F m, fixpoint F (gfp F m).
split. destruct 1. apply (m _ _ H). assumption.
intro. apply gfp_roll with (gfp F m). trivial. assumption.
Qed.

Lemma gfp_greatest : forall F m X, fixpoint F X ->
  (forall a, X a -> gfp F m a).
Proof. intros F m X H.
cofix. intros.
econstructor. apply gfp_greatest. apply H. assumption.
Qed.

Lemma gfp_coinduction : forall (X : A -> Prop) F (m : mono F),
  (forall a, X a -> F X a) ->
  (forall a, X a -> gfp F m a).
intros X F m H. cofix.
intros. econstructor. eassumption. apply H. assumption.
Qed.

Definition close F (m : mono F) (X : A -> Prop) : A -> Prop.
  refine (lfp (fun Y a => F Y a \/ X a) _).
  abstract (unfold mono;intros;destruct H0;[left;revert H0;apply m|right];assumption).
Defined.

Definition close_idem F (m : mono F) (X : A -> Prop) :
  forall a, close F m (close F m X) a -> close F m X a.
apply lfp_induction. destruct 1;[ |assumption].
apply lfp_fixes. left. assumption.
Qed.

Lemma close_greater F (m : mono F) (X : A -> Prop) :
  forall a, X a -> close F m X a.
Proof. intros. apply lfp_fixes. right. assumption. Qed.

Lemma close_unroll F (m : mono F) (X : A -> Prop) :
  forall a, F (close F m X) a -> close F m X a.
Proof. intros. apply lfp_fixes. left. assumption. Qed.

Lemma main : forall F G (mF : mono F) (mG : mono G)
   (H : forall A a, G (F A) a -> F (close G mG A) a)
   (X : A -> Prop),
   (forall a, X a -> F (close G mG X) a) ->
   (forall a, X a -> gfp F mF a).
intros F G mF mG H X pf.
intros. assert (close G mG X a).
clear -H0. apply lfp_fixes. right. assumption.
clear H0. revert a H1.
apply gfp_coinduction.
apply lfp_induction.
destruct 1;[ |apply pf;assumption].
apply H in H0. revert a H0. apply mF.
apply close_idem.
Qed.
End Lattice.

Definition uncurry {A B C : Type} (f : A -> B -> C) : (A * B) -> C :=
  fun ab => f (fst ab) (snd ab).
Definition curry {A B C : Type} (f : A * B -> C) : A -> B -> C :=
  fun a b => f (a,b).

Add LoadPath "../common".
Require proof.

Section Programs.
Variable cfg : Set.
Variable cstep : cfg -> cfg -> Prop.

Definition claim := (cfg * (cfg -> Prop))%type.
Definition Spec : Type := claim -> Prop.

Definition pf_Spec := proof.Spec cfg.
Definition pf_step : pf_Spec -> pf_Spec := proof.step cstep.
Definition pf_trans : pf_Spec -> pf_Spec := proof.trans cstep.
Definition pf_reaches : pf_Spec := proof.reaches cstep.
Definition pf_sound : pf_Spec -> Prop := proof.sound cstep.

Definition step (X : Spec) : Spec := uncurry (pf_step (curry X)).
Definition trans (X : Spec) : Spec := uncurry (pf_trans (curry X)).

Lemma step_mono : mono _ step.
unfold mono,step. intros until a.
destruct a; unfold uncurry; simpl.
destruct 1.
* apply proof.sdone. assumption.
* eapply proof.sstep. eassumption. revert H1. apply H.
Qed.

Lemma trans_mono : mono _ trans.
Proof.
unfold mono,trans,curry,uncurry. destruct a;simpl.
induction 1;simpl;econstructor(solve[eauto]).
Qed.

Lemma reaches_greatest : forall (x : claim),
  gfp _ _ step_mono x -> uncurry pf_reaches x.
Proof.
destruct x;unfold uncurry;simpl;intro.
eapply proof.stable_sound with (Rules:=curry (gfp _ _ step_mono));[|assumption].
intros. apply gfp_fixes in H0. destruct H0;econstructor(eassumption).
Qed.

Lemma trans_valid : forall (A : claim -> Prop) (a : claim),
   trans (step A) a -> step (close claim trans trans_mono A) a.
destruct a. unfold trans at 1,step at 2,uncurry;simpl. induction 1.
* constructor(assumption).
* clear H. destruct IHtrans. solve[auto].
  eapply proof.sstep. eassumption. clear H k.
  apply close_unroll. eapply proof.dtrans. eassumption.
    simpl. clear k' H2.
    intros. specialize (H1 _ H).
  clear - H1. destruct H1;solve[eauto using proof.trans].
* destruct H.
    econstructor(eassumption).
    eapply proof.sstep. eassumption.
    apply close_greater. assumption.
* clear H0.
  eapply proof.sstep with (1:=H); clear k H.
  apply close_unroll. unfold trans at 1,uncurry;simpl.
  destruct IHtrans;econstructor(solve[eauto using proof.trans]).
Qed.
End Programs.

(* Give a name for the type of proof.proved_sound *)
Definition soundness_lemma : Type.
let T := type of (@proof.proved_sound) in exact T.
Defined.
(* Check that proof.proved_sound actually has that type *)
Definition pf_soundness : soundness_lemma := @proof.proved_sound.

Lemma main' : soundness_lemma.
intros cfg cstep.
unfold pf_sound, proof.sound. intros.
change (uncurry (pf_reaches _ cstep) (x,P)).
apply reaches_greatest.
change (uncurry Rules (x,P)) in H0. revert H0.
eapply main with (mG:=(trans_mono _ cstep)).

exact (trans_valid cfg cstep).

clear -H.
destruct a. intro. apply H in H0.
destruct H0. constructor(assumption).
eapply proof.sstep. eassumption.
unfold curry;simpl.
change (trans _ cstep (uncurry Rules) (k', P)) in H1.
apply close_unroll.
revert H1. apply trans_mono. clear;intros. apply lfp_fixes.  right. assumption.
Qed.
