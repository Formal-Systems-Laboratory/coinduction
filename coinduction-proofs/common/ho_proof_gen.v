Require Import Morphisms.

Set Implicit Arguments.

Section relations.
Variables (cfg : Type) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> Prop) -> Prop.
Definition subspec (A B:Spec) : Prop := forall k P, A k P -> B k P.
Definition mono (F : Spec -> Spec) : Prop := Proper (subspec ==> subspec) F.
Definition ho_mono (F : (Spec -> Spec) -> (Spec -> Spec)) : Prop
  := Proper ((subspec ==> subspec) ==> (subspec ==> subspec)) F.

(* t : Spec -> Spec *)
Inductive t (b : Spec -> Spec) (X : Spec) : Spec :=
| t_def : forall Y, mono Y -> (forall A, subspec (Y (b A)) (b (Y A)))
                    -> subspec (Y X) (t b X).

Lemma t_mono : forall b, mono (t b).
Proof. destruct 2. econstructor. eauto. eauto. revert H2. apply H0. assumption. Qed.

Lemma t_base : forall X b, mono b -> subspec (b X) (t b X).
Proof.
  unfold subspec;intros. eapply t_def with (b:=b).
  eassumption. firstorder. assumption.
Qed.

Lemma t_id : forall (X:Spec) (b:Spec -> Spec), subspec X (t b X).
Proof.
  unfold subspec;intros.
  eapply t_def with (Y := fun X => X) (b := b). unfold mono. firstorder. firstorder. trivial.
Qed.

Lemma t_compat : forall (X:Spec) b, mono b -> subspec (t b (b X)) (b (t b X)).
Proof. unfold subspec. intros. destruct H0. eapply H1 in H2.
       revert H2. apply H. eapply t_def;eauto. Qed.

Lemma t_idem : forall X b, mono b -> subspec (t b (t b X)) (t b X).
Proof. unfold subspec. intros. apply t_def with (fun X => t b (t b X)).
       intro. intros;intro;intros. revert H2. apply t_mono.
       intros;intro;intros. revert H2. apply t_mono. trivial.
       intros. intro. intros. apply t_compat. assumption. 
       revert H1. eapply t_mono. apply t_compat. assumption.
       assumption.
Qed.

Lemma t_ext : forall Rules b,
    mono b -> subspec Rules (b (t b Rules)) -> subspec (t b Rules) (b (t b Rules)).
Proof. intros. unfold subspec. intros. apply (t_mono H0) in H1. apply t_compat in H1.
       revert H1. eapply H. apply t_idem. assumption. assumption. Qed.


Lemma t_rule : forall (F : Spec -> Spec) b, mono F -> mono b ->
                  (forall X, subspec (F X) (t b X)) ->
                  forall A, subspec (F (t b A)) (t b A).
Proof. intros. unfold subspec;intros. eapply t_idem. apply H0. revert H2. apply H1. Qed.

(* A higher order function so F <= Step F exactly when F is compatible, i.e. F o step <= step o F
   Thus t is the greatest fixpoint of B
 *)

Inductive B (b : Spec -> Spec) (F : Spec -> Spec) (X : Spec) k (P:cfg -> Prop) : Prop :=
| B_def : forall G, mono G
                       -> (forall A, subspec (G (b A)) (b (F A)))
                       -> G X k P -> B b F X k P.
(* T is related to Step as t is related to step.
   F <= B (T F) implies F <= t
 *)
Inductive T (b : Spec -> Spec) (F: Spec -> Spec) (X : Spec) : Spec :=
  (* trans : Spec -> Spec *)
| T_def : forall Y, ho_mono Y
                    -> (forall G A, mono G -> subspec (Y (B b G) A) (B b (Y G) A))
                    -> subspec (Y F X) (T b F X).

Lemma B_mono : forall b, mono b -> ho_mono (B b).
Proof. destruct 4. apply B_def with G. assumption.
       intros. intro;intros. apply H3 in H5. revert H5. apply H. apply H0. firstorder.
       revert H4. apply H2. assumption.
Qed.

Lemma T_mono : forall b, ho_mono (T b).
Proof. destruct 3. econstructor;try eassumption. revert H3. apply H1.
       apply H. assumption.
Qed.

Lemma Tf_id : forall b (F : Spec -> Spec), forall A, subspec A (T b F A).
Proof.
  Ltac T_finish Q := apply T_def with Q;[solve[firstorder]|..|assumption];
   let G:=fresh "G" in intro G;unfold subspec;intros;
   try solve[apply B_def with (Q G);[firstorder..|assumption]].
 Ltac T_solve :=
     match goal with
     | [|- forall b F A, subspec (@?Q F A) (T b F A) ] => 
                     intros b F A;intro;intros;T_finish Q
     | [|- forall b F A, mono F -> subspec (@?Q F A) (T b F A) ] => 
                     intros b F A HF;intro;intros;T_finish Q
     | [|- forall b F A, mono F -> forall A, subspec (@?Q F A) (T b F A) ] => 
                     intros b F HF A;intro;intros;T_finish Q
     end.
  T_solve.
Qed.

Lemma Tf_base : forall b (F : Spec -> Spec), forall A, mono b -> subspec (b A) (T b F A).
Proof.
  intros;intro;intros.
  eapply T_def with (fun X => b). firstorder. intros. 
  intros;intro;intros. 
  eapply B_def. apply H. intros. firstorder. trivial. trivial.
Qed.

Lemma T_id : forall b (F : Spec -> Spec), forall A, subspec (F A) (T b F A).
Proof.
  intros;intro;intros.
  eapply T_def with (fun X => X). firstorder. intros. firstorder. trivial.
Qed.

Lemma T_compat: forall b F, mono b -> mono F -> forall A,
                                subspec (T b (B b F) A) (B b (T b F) A).
Proof.
  intros;intro;intros.
  destruct H1.
  apply H2 in H3;[|assumption].
  revert H3. apply B_mono. assumption.
  intro;intros;intro;intros. apply T_def with Y;try assumption.
  revert H4. apply H1. firstorder. trivial. firstorder.
Qed.

Lemma T_idem : forall b (F : Spec -> Spec),
    mono b -> forall A, subspec (T b (T b F) A) (T b F A).
Proof.
  intros;intro;intros.
  eapply T_def with (fun F => T b (T b F));[..|assumption].
  intro;intros. apply T_mono. apply T_mono;assumption.
  intros. intro;intros. apply T_compat. assumption. apply T_mono; assumption.
  revert H2. apply T_mono;[|firstorder].
  intro;intros. intro;intros. apply T_compat. assumption. assumption.
  revert H3. apply T_mono. apply B_mono. assumption. firstorder. assumption.
Qed.

Definition bot (x:cfg) (P : cfg -> Prop) : Prop := False.

Lemma Tbot_compat : forall b (X:Spec),
    mono b -> subspec (T b (fun _ => bot) (b X)) (b (T b (fun _ => bot) X)).
Proof.
  intros;intro;intros. destruct H0. edestruct H1. 
  assert (mono (fun _ => bot)). firstorder. apply H3.
  eapply H0. Focus 3. apply H2. firstorder.
  intro;intros. eassumption.
  apply H4 in H5. revert H5. apply H.
  intro;intros. eapply T_def; try eassumption.
Qed.

Lemma T_t : forall b A, subspec (t b A) (T b (fun _ => bot) A).
Proof.
  destruct 1.
  apply T_def with (fun _ => Y);[firstorder| |assumption].
  unfold subspec;intros.
  apply B_def with Y;auto.
Qed.

Lemma t_T : forall b A, mono b -> subspec (T b (fun _ => bot) A) (t b A).
Proof.
  intros;intro;intros.
  eapply t_def. apply T_mono. Focus 3. eassumption. firstorder.
  intros;intro;intros. apply Tbot_compat; trivial.
Qed.


Lemma Tf_t : forall b F A, mono F -> subspec (t b A) (T b F A).
Proof.
  unfold subspec;intros.
  apply T_t in H0. revert H0.
  apply T_mono. firstorder.
  unfold subspec;trivial.
Qed.

Lemma dup_compat : forall b F A, mono b -> mono F ->
   subspec (B b F (B b F A)) (B b (fun A => F (F A)) A).
Proof.
  intros. intro;intros.
  apply B_def with (G:=(fun A => B b F (B b F A)));[..|assumption].
  intro;intros. apply B_mono. assumption. trivial. apply B_mono; trivial.
  intros;intro;intros.
  assert (forall X, subspec (B b F (b X)) (b (F X))).
  intros;intro;intros. destruct H3. apply H4. assumption.
  apply H3. revert H2. apply B_mono; trivial.
Qed.

Lemma Tf_idem : forall b (F : Spec -> Spec),
    mono b -> mono F -> forall A, subspec (T b F (T b F A)) (T b F A).
Proof.
  intros;intro;intros.
  apply T_idem. assumption. apply T_def with (fun F A => F (F A));[..|assumption].
  intro;intros;intro;intros. apply H2. apply H2. assumption.
  intros. apply dup_compat; trivial.
Qed.

Lemma tfun : forall b (F : Spec -> Spec),
    mono b -> mono F -> forall A, subspec (F (T b F A)) (T b F A).
Proof.
  intros;intro;intros. apply Tf_idem; try assumption. apply T_id. assumption.
Qed.
  
Lemma t_gfp : forall b (F : Spec -> Spec), mono F ->
    (forall A, subspec (F A) (B b F A)) ->
    (forall A, subspec (F A) (t b A)).
intros;intro;intros.
apply t_def with F;try assumption.
intros;intro;intros. 
destruct (H0 (b A0) _ _ H2).
apply H4. assumption.
Qed.

Lemma t_gfp_help : forall b (F : Spec -> Spec), mono F ->
    (forall A, subspec ((T b F) A) (B b (T b F) A)) ->
    (forall A, subspec ((T b F) A) (t b A)).
Proof.
  intros. apply t_gfp. apply T_mono. eauto. assumption. 
Qed.

Lemma t_gfp' : forall b (F : Spec -> Spec), mono b -> mono F ->
    (forall A, subspec (F A) (B b (T b F) A)) ->
    (forall A, subspec (F A) (t b A)).
Proof.
  intros. assert (subspec (F A) (B b (T b F) A)) by apply H1.  
  assert (forall A, subspec ((T b F) A) (T b (B b (T b F)) A)). (* assumption, mono of T *)
  intros;intro;intros. eapply T_mono. Focus 3. eapply H3. firstorder. firstorder.
  assert (forall A, subspec (T b (B b (T b F)) A) (B b (T b (T b F)) A)).
  intros;intro;intros. apply T_compat. assumption. apply T_mono. eauto. trivial.
  assert (forall A, subspec (B b (T b (T b F)) A) (B b (T b F) A)). (* idempotency of T *)
  intros;intro;intros. revert H5. apply B_mono. assumption. intro;intros;intro;intros.
  eapply T_idem. apply H. revert H6. apply T_mono. apply T_mono. trivial. trivial. firstorder.
  assert (forall A, subspec ((T b F) A) (B b (T b F) A)).
  intros;intro;intros. apply H5. apply H4. apply H3. trivial.
  eapply t_gfp_help with (A:=A) in H6.
  intro;intros. apply H6. apply T_id. trivial. trivial.
Qed.
  
Lemma T_rule_f : forall b F, mono b -> mono F ->
                             (forall A, subspec (F A) (t b A)) ->
                           (forall A, subspec (T b F A) (t b A)).
Proof.
  intros;intro;intros.
  assert (forall A, subspec (T b F A) (T b (t b) A)).
  intros. apply T_mono; firstorder.
  pose proof T_t.
  assert (forall A, subspec (T b F A) (T b (T b (fun _ => bot)) A)).
  intros. 
  intro;intros. apply H3 in H5. inversion H5; subst.  
  eapply T_def. eassumption. apply H7. revert H8. apply H6.
  intro;intros;intro;intros. apply H4. revert H9. apply t_mono. trivial.
  firstorder.
  eapply T_idem in H5.
  pose proof t_T. apply H6. assumption. eassumption. trivial. trivial.
Qed.

Lemma rule_by_T : forall b (F : Spec -> Spec), mono b -> mono F ->
    (forall A, subspec (F (b A)) (b (T b F A))) -> (forall A, subspec (F A) (t b A)).
  (* true by lemma 6.2 and fb <= b(Tf) ==> f <= B(Tf) ==> f <= Bdag f ==> f <= t *)
  intros. apply t_gfp'. apply H. apply H0.
  intros. unfold subspec. intros. apply B_def with (G := F).
  apply H0. apply H1. trivial.
Qed.

Lemma use_step : forall b F, mono b -> mono F -> forall A, subspec (b (T b F A)) (T b F A).
Proof.
  unfold subspec;intros. apply Tf_idem; try assumption. apply Tf_base; auto.
Qed.


End relations.
