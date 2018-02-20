Require Import ho_proof_gen.

Set Implicit Arguments.

Section step_all.

Variables (cfg : Type) (cstep : cfg -> cfg -> Prop).
Definition Spec : Type := cfg -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive reaches (k : cfg) (P : cfg -> Prop) : Prop :=
  | rdone : P k -> reaches k P
  | rstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> reaches k' P) -> reaches k P.

Definition sound Rules : Prop := subspec Rules reaches.

Inductive step (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step X k P
  | sstep : (exists k', cstep k k') ->
            (forall k', cstep k k' -> X k' P) -> step X k P.

Lemma step_mono : mono step.
Proof. destruct 2;econstructor(solve[eauto using step]). Qed.

Lemma reaches_stable : subspec reaches (step reaches).
Proof. destruct 1; econstructor(assumption). Qed.

CoFixpoint stable_sound Rules (Hstable : subspec Rules (step Rules)) : sound Rules :=
  fun x P H =>
  match Hstable _ _ H with
    | sdone pf => rdone _ _ pf
    | sstep prog pres => rstep prog
       (fun k' Hstep => stable_sound Hstable k' _ (pres k' Hstep))
  end.

Lemma proof_by_t : forall (Rules : Spec), subspec Rules (step (t step Rules)) -> sound Rules.
  intros. apply t_ext in H. apply stable_sound in H. revert H.
  unfold sound, subspec. firstorder using t_id. apply step_mono. 
Qed.

Definition trans (X:Spec) : Spec := fun k P => exists Q, X k Q /\ (forall k', Q k' -> X k' P).

Lemma mono_trans : mono trans.
Proof.
  destruct 2. inversion H0. econstructor; split. apply H. eassumption.
  intros. apply H. apply H2. trivial.
Qed.

(*T step trans A k' Q Q' /\ (forall k'0 : cfg, Q' k'0 -> T step trans A k'0 Q P)*)

Lemma trans_ok_rule : forall X, subspec (trans X) (t step X).
  apply rule_by_T. apply step_mono. apply mono_trans.
  unfold subspec. intros. destruct H as [Q [HQ H]].
  destruct HQ. specialize (H _ H0). revert H. apply step_mono. apply Tf_id.
  eapply sstep;eauto. intros. apply Tf_idem. apply step_mono.
  firstorder. apply T_id.
  exists Q. split. eapply Tf_id;apply H1;assumption. intros.
  specialize (H k'0 H3). apply Tf_base. apply step_mono. assumption.
Qed.

Lemma use_trans : forall A, subspec (trans (t step A)) (t step A).
apply t_rule. firstorder. apply step_mono. apply trans_ok_rule.
Qed.

Lemma tstep: forall F, mono F -> forall A x P,
      (exists x', cstep x x') -> (forall x', cstep x x' -> T step F A x' P) -> T step F A x P.
Proof.
  intros. apply use_step. apply step_mono. assumption. eapply sstep. assumption. assumption.
Qed.

Lemma tdone: forall F, mono F -> forall A x (P:cfg->Prop), P x -> T step F A x P.
Proof.
  intros. apply use_step. apply step_mono. assumption. eapply sdone;eassumption.
Qed.

Lemma ttrans: forall F, mono F -> forall A x Q P,
    T step F A x Q -> (forall y, Q y -> T step F A y P) -> T step F A x P.
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
Lemma ok : forall F, mono F ->
    (forall A, subspec (F A) (step (T step F A))) ->
    (forall X, subspec X (F X) -> subspec X reaches)
    (* == subspec (gfp F) reaches *).
  intros.
  assert (forall A, subspec (F A) (t step A)).
  intros. apply rule_by_T. apply step_mono. apply H.  
  unfold subspec;intros. apply H0 in H2. revert H2. apply step_mono.
  unfold subspec;intros. apply Tf_idem. apply step_mono. assumption.
  revert H2. apply T_mono. assumption. apply Tf_base. apply step_mono.
  apply proof_by_t. intro;intros.
  apply H1 in H3. apply H0 in H3.
  revert H3. apply step_mono. apply T_rule_f. apply step_mono. assumption. assumption.
Qed.

End step_all.
