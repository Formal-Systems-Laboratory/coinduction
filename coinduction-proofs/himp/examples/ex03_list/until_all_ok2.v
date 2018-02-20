Require Import ho_proof_until_gen.

Set Implicit Arguments.

Section until_all.

Variables (cfg : Type) (cstep : cfg -> cfg -> Prop).
Definition Spec : Type := cfg -> (cfg -> cfg -> Prop) -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive until (k : cfg) (R : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | rdone : P k -> until k R P
  | rstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> R k k' /\ until k' R P) -> until k R P.

Definition sound (A : Set) (Rules : Spec) : Prop := subspec Rules until.

Inductive step (A : Set) (X : Spec) (k : cfg) (R : cfg -> cfg -> Prop) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step A X k R P
  | sstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> R k k' /\ X k' R P) -> step A X k R P.

Lemma step_mono : forall A, mono (step A).
Proof.
  destruct 2. constructor. assumption.
  apply sstep. assumption. intros. split. Focus 2. apply H.
  eapply H1. assumption. eapply H1. assumption.
Qed.

Lemma until_stable : forall A, subspec until (step A until).
Proof. destruct 1; econstructor(assumption). Qed.

CoFixpoint stable_sound A (Rules : Spec)
  (Hstable : forall x R P, Rules x R P -> step A Rules x R P)
  : sound A Rules := fun x R P H =>
match Hstable _ _ _ H with
    | sdone pf => rdone _ _ _ pf
    | sstep not_stuck Hsteps => rstep not_stuck (fun k' Hstep =>
        let (Hpres, Hk') := Hsteps k' Hstep
        in conj Hpres (stable_sound Hstable k' R P Hk'))
end.

Lemma proof_by_t : forall (A : Set) (Rules : Spec), subspec Rules (step A (t (step A) Rules)) -> sound A Rules.
  intros. apply t_ext in H. apply stable_sound in H. revert H.
  unfold sound, subspec. intros. apply H. apply t_id. trivial. apply step_mono. 
Qed.

Definition trans (X:Spec) : Spec :=
  fun k R P => exists Q, X k R Q /\ (forall k', Q k' -> X k' R P).

Lemma mono_trans : mono trans.
Proof.
  destruct 2. inversion H0. econstructor; split. apply H. eassumption.
  intros. apply H. apply H2. trivial.
Qed.

Lemma trans_ok_rule : forall A X, subspec (trans X) (t (step A) X).
  intro A. apply rule_by_T. apply step_mono. apply mono_trans.
  unfold subspec. intros. destruct H as [Q' [HQ' H]].
  destruct HQ'. specialize (H _ H0). revert H. apply step_mono. apply Tf_id.
  eapply sstep;eauto. intros. split. apply H1. assumption.
  apply Tf_idem. apply step_mono. apply mono_trans.
  apply T_id. exists Q'. split. apply Tf_id. apply H1. assumption.
  intros. specialize (H k'0 H3). apply Tf_base. apply step_mono. assumption.
Qed.

Lemma use_trans : forall A B, subspec (trans (t (step A) B)) (t (step A) B).
intro A. apply t_rule. firstorder. apply step_mono. apply trans_ok_rule.
Qed.

Lemma tstep: forall F, mono F -> forall B A x R P,
      (exists x', cstep x x') ->
      (forall x', cstep x x' -> R x x' /\ T (step B) F A x' R P) -> T (step B) F A x R P.
Proof.
  intros. apply use_step. apply step_mono. assumption. eapply sstep. assumption. assumption.
Qed.

Lemma tdone: forall F, mono F -> forall B A x R (P:cfg->Prop), P x -> T (step B) F A x R P.
Proof.
  intros. apply use_step. apply step_mono. assumption. eapply sdone;eassumption.
Qed.

Lemma ttrans: forall F, mono F -> forall B A x R Q P,
    T (step B) F A x R Q -> (forall y, Q y -> T (step B) F A y R P) -> T (step B) F A x R P.
Proof.
  intros. apply Tf_idem. apply step_mono. assumption. apply Tf_t. assumption.
  apply trans_ok_rule. unfold trans. exists Q.
  split;assumption.
Qed.

(* X <= step(t X) ==> X <= gfp step *)
(* X <= Step (T X) *)
(* X (step A) <= step ((T X) A) ==> X <= t
   ==> X reaches <= reaches, other stuff *)

(* t_|_ = gfp step ==> t (gfp step) = t (t _|_) = t bot = gfp step *)

(* F : higher order spec  *)
(* F(A) <= step((T F) A)  *)
(* gfp F <= reaches *)
Lemma ok : forall B F, mono F ->
    (forall A, subspec (F A) (step B (T (step B) F A))) ->
    (forall X, subspec X (F X) -> subspec X until)
    (* == subspec (gfp F) reaches *).
  intros.
  assert (forall A, subspec (F A) (t (step B) A)).
  intros. apply rule_by_T. apply step_mono. apply H.  
  unfold subspec;intros. apply H0 in H2. revert H2. apply step_mono.
  unfold subspec;intros. apply Tf_idem. apply step_mono. assumption.
  revert H2. apply T_mono. assumption. apply Tf_base. apply step_mono.
  eapply proof_by_t. intro;intros.
  apply H1 in H3. apply H0 in H3.
  revert H3. apply step_mono. apply T_rule_f. apply step_mono. assumption. assumption.
Qed.

End until_all.

