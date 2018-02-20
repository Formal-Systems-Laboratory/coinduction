Require Import Morphisms.

Set Implicit Arguments.

(* How to only request that things work ok on well-behaved elements? *)
Record semilattice (D : Type) (R : D -> D -> Prop) 
  (T:Transitive R) :=
  (* transitivity too *)
  {close : D -> D
  ;close_proper : forall d, Proper R (close d)
  ;close_upper : forall d, R d (close d)
  ;close_least : forall d d', R d d' -> Proper R d' -> R (close d) d'
  ;lub : (D -> Prop) -> D
  ;lub_proper : forall H, Proper R (lub H)
  ;lub_upper : forall (H:D->Prop) d, H (close d) -> R (close d) (lub H)
  ;lub_least : forall (H:D->Prop) u, Proper R u
    -> (forall d, H (close d) -> R (close d) u) -> R (lub H) u
  }.

(* Definition fun_lattice D R T (L : @semilattice D R T) *)
(*            : semilattice (R ==> R)%signature ?. *)
(* Proof. *)
(*   apply Build_semilattice with *)
(*   (close:=fun F x => lub L (fun y => exists x', R x' x /\ R y (F x'))) *)
(*   (lub:=fun H x => lub L (fun u => exists F, Proper (R ==> R) F /\ R u (F x))). *)
(*   (* close_proper *) *)
(*   intros;intro;intros. *)
(*      apply lub_least. apply lub_proper. intros. apply lub_upper. *)
(*      destruct H0. destruct H0. exists x0. split;[|assumption]. admit. *)
(*   (* close_upper *) *)
(*   intros;intro;intros. transitivity (close L (d x)). *)

     
(*   intros;intro;intros. apply (lub_upper L). apply H0. *)
(*   replace (d x) with (d y). *)
(*   apply (lub_upper L). apply H0. *)

(* Section companion. *)
(*   Variables (D : Type) (R : D -> D -> Prop) *)
(*   Variables (base : D -> D) (base_mono : Proper (R ==> R) base). *)

(*   Definition t : D -> D := lub (fun Y => forall A, R (Y (base A)) (base (Y A))). *)
(* End companion. *)

Section relations.
Variables (cfg : Type) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> Prop) -> Prop.
Definition subspec (A B:Spec) : Prop := forall k P, A k P -> B k P.
Definition mono (F : Spec -> Spec) : Prop := Proper (subspec ==> subspec) F.
Definition ho_mono (F : (Spec -> Spec) -> (Spec -> Spec)) : Prop
  := Proper ((subspec ==> subspec) ==> (subspec ==> subspec)) F.

(* Soundness *)
CoInductive reaches (k : cfg) (P : cfg -> Prop) : Prop :=
  (* reaches : Spec, but defining k and P as parameters
     gives a cleaner definition and induction principle. *)
| rdone : P k -> reaches k P
| rstep : forall k', cstep k k' -> reaches k' P -> reaches k P.

Definition sound Rules : Prop := subspec Rules reaches.

Inductive step (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  (* step : Spec -> Spec *)
| sdone : P k -> step X k P
| sstep : forall k', cstep k k' -> X k' P -> step X k P.
Lemma step_mono : mono step.
Proof. destruct 2;econstructor(solve[eauto using step]). Qed.

Lemma reaches_stable : subspec reaches (step reaches).
Proof. destruct 1;econstructor(eassumption). Qed.

CoFixpoint stable_sound Rules (Hstable : subspec Rules (step Rules)) : sound Rules :=
  fun x P H =>
  match Hstable _ _ H with
    | sdone pf => rdone _ _ pf
    | sstep k' Hstep H' =>
        rstep Hstep (stable_sound Hstable _ _ H')
  end.

(* t : Spec -> Spec *)
Inductive t (X : Spec) : Spec :=
| t_def : forall Y, mono Y -> (forall A, subspec (Y (step A)) (step (Y A)))
                    -> subspec (Y X) (t X).

Lemma t_mono : mono t.
Proof. destruct 2. econstructor. eauto. eauto. revert H2. apply H0. assumption. Qed.
Lemma t_base : forall X, subspec (step X) (t X).
Proof. unfold subspec;intros. apply t_def with step. apply step_mono. firstorder. assumption. Qed.
Lemma t_id : forall (X:Spec), subspec X (t X).
Proof.
  unfold subspec;intros.
  apply t_def with (fun X => X);unfold mono;trivial || firstorder.
Qed.
Lemma t_compat : forall (X:Spec), subspec (t (step X)) (step (t X)).
Proof. unfold subspec. intros. destruct H. apply H0 in H1.
       revert H1. apply step_mono. eapply t_def;eauto. Qed.
Lemma t_idem : forall X, subspec (t (t X)) (t X).
Proof. unfold subspec. intros. apply t_def with (fun X => t (t X)).
       intro. intros. eauto using t_mono.
       intros. intro. intros. apply t_compat. revert H0. apply t_mono. apply t_compat.
       assumption.
Qed.

Lemma t_ext : forall Rules, subspec Rules (step (t Rules)) -> subspec (t Rules) (step (t Rules)).
Proof. intros. unfold subspec. intros. apply (t_mono H) in H0. apply t_compat in H0.
       revert H0. apply step_mono. apply t_idem. Qed.

Lemma proof_by_t : forall (Rules : Spec), subspec Rules (step (t Rules)) -> sound Rules.
  intros. apply t_ext in H. apply stable_sound in H. revert H.
  unfold sound, subspec. firstorder using t_id.
Qed.

Lemma t_rule : forall (F : Spec -> Spec), mono F -> (forall X, subspec (F X) (t X)) ->
                  forall A, subspec (F (t A)) (t A).
Proof. intros. unfold subspec;intros. eapply t_idem. revert H1. apply H0. Qed.

(* A higher order function so F <= Step F exactly when F is compatible, i.e. F o step <= step o F
   Thus t is the greatest fixpoint of B
 *)
Inductive Step (F : Spec -> Spec) (X : Spec) k (P:cfg -> Prop) : Prop :=
| Step_def : forall G, mono G
                       -> (forall A, subspec (G (step A)) (step (F A)))
                       -> G X k P -> Step F X k P.
(* T is related to Step as t is related to step.
   F <= B (T F) implies F <= t
 *)
Inductive T (F: Spec -> Spec) (X : Spec) : Spec :=
  (* trans : Spec -> Spec *)
| T_def : forall Y, ho_mono Y
                    -> (forall G A, mono G -> subspec (Y (Step G) A) (Step (Y G) A))
                    -> subspec (Y F X) (T F X).

Lemma Step_mono : ho_mono Step.
Proof. destruct 3. apply Step_def with G. assumption.
       intros. intro;intros. apply H2 in H4. revert H4. apply step_mono. apply H. firstorder.
       revert H3. apply H1. assumption.
Qed.

Lemma T_mono : ho_mono T.
Proof. destruct 3. econstructor;try eassumption. revert H3. apply H1.
       apply H. assumption.
Qed.

Lemma Tf_id : forall (F : Spec -> Spec), forall A, subspec A (T F A).
Proof.
  Ltac T_finish Q := apply T_def with Q;[solve[firstorder using step_mono]|..|assumption];
   let G:=fresh "G" in intro G;unfold subspec;intros;
   try solve[apply Step_def with (Q G);[firstorder using step_mono..|assumption]].
 Ltac T_solve :=
     match goal with
     | [|- forall F A, subspec (@?Q F A) (T F A) ] =>
                     intros F A;intro;intros;T_finish Q
     | [|- forall F A, mono F -> subspec (@?Q F A) (T F A) ] =>
                     intros F A HF;intro;intros;T_finish Q
     | [|- forall F, mono F -> forall A, subspec (@?Q F A) (T F A) ] =>
                     intros F HF A;intro;intros;T_finish Q
     end.
  T_solve.
Qed.

Lemma Tf_base : forall (F : Spec -> Spec), forall A, subspec (step A) (T F A).
Proof.
  T_solve.
Qed.

Lemma T_id : forall (F : Spec -> Spec), forall A, subspec (F A) (T F A).
Proof.
  T_solve.
  trivial.
Qed.

Lemma T_compat: forall F, mono F -> forall A, subspec (T (Step F) A) (Step (T F) A).
Proof.
  intros;intro;intros.
  destruct H0.
  apply H1 in H2;[|assumption].
  revert H2. apply Step_mono;[|firstorder].
  intro;intros. intro;intros. apply T_def with Y;try assumption.
  revert H3. apply H0;trivial.
Qed.

Lemma T_idem : forall (F : Spec -> Spec), forall A, subspec (T (T F) A) (T F A).
Proof.
  intros;intro;intros.
  eapply T_def with (fun F => T (T F));[..|assumption].
  intro;intros. apply T_mono. apply T_mono;assumption.
  intros. intro;intros. apply T_compat. apply T_mono; assumption.
  revert H1. apply T_mono;[|firstorder].
  intro;intros. intro;intros. apply T_compat. assumption.
  revert H2. apply T_mono. apply Step_mono. assumption. assumption.
Qed.

Definition bot (x:cfg) (P : cfg -> Prop) : Prop := False.

Lemma Tbot_compat : forall (X:Spec),
    subspec (T (fun _ => bot) (step X)) (step (T (fun _ => bot) X)).
Proof.
  intros;intro;intros. destruct H. edestruct H0. 
  assert (mono (fun _ => bot)). firstorder. apply H2.
  eapply H. Focus 3. apply H1. firstorder.
  intro;intros. eassumption.
  edestruct H3. eassumption.
  constructor. trivial.
  eapply sstep. eassumption.
  eapply T_def. apply H. assumption. trivial.
Qed.

Lemma T_t : forall A, subspec (t A) (T (fun _ => bot) A).
Proof.
  destruct 1.
  apply T_def with (fun _ => Y);[firstorder| |assumption].
  unfold subspec;intros.
  apply Step_def with Y;auto.
Qed.

Lemma t_T : forall A, subspec (T (fun _ => bot) A) (t A).
Proof.
  intros;intro;intros.
  eapply t_def; try eassumption. apply T_mono. firstorder.
  intros;intro;intros. apply Tbot_compat. trivial.
Qed.


Lemma Tf_t : forall F A, mono F -> subspec (t A) (T F A).
Proof.
  unfold subspec;intros.
  apply T_t in H0. revert H0.
  apply T_mono. firstorder.
  unfold subspec;trivial.
Qed.

Lemma dup_compat : forall F A, mono F ->
   subspec (Step F (Step F A)) (Step (fun A => F (F A)) A).
Proof.
  intros. intro;intros.
  apply Step_def with (G:=(fun A => Step F (Step F A)));[..|assumption].
  intro;intros. apply Step_mono. trivial. apply Step_mono;trivial.
  intros;intro;intros.
  assert (forall X, subspec (Step F (step X)) (step (F X))).
  intros;intro;intros. destruct H2. apply H3. assumption.
  apply H2. revert H1. apply Step_mono. trivial.
  apply H2.
Qed.

Lemma Tf_idem : forall (F : Spec -> Spec), mono F ->
                                           forall A, subspec (T F (T F A)) (T F A).
Proof.
  intros;intro;intros.
  apply T_idem. apply T_def with (fun F A => F (F A));[..|assumption].
     intro;intros;intro;intros. apply H1. apply H1. assumption.
  apply dup_compat.
Qed.

Lemma tfun : forall (F : Spec -> Spec), mono F ->
                                         forall A, subspec (F (T F A)) (T F A).
Proof.
  intros;intro;intros. apply Tf_idem. assumption. apply T_id. assumption.
Qed.
  
Lemma t_gfp : forall (F : Spec -> Spec), mono F ->
    (forall A, subspec (F A) (Step F A)) ->
    (forall A, subspec (F A) (t A)).
intros;intro;intros.
apply t_def with F;try assumption.
intros;intro;intros. 
destruct (H0 (step A0) _ _ H2).
apply H4. assumption.
Qed.

Lemma t_gfp_help : forall (F : Spec -> Spec), mono F ->
    (forall A, subspec ((T F) A) (Step (T F) A)) ->
    (forall A, subspec ((T F) A) (t A)).
Proof.
  intros. apply t_gfp. apply T_mono. eauto. assumption. 
Qed.

Lemma t_gfp' : forall (F : Spec -> Spec), mono F ->
    (forall A, subspec (F A) (Step (T F) A)) ->
    (forall A, subspec (F A) (t A)).
Proof.
  intros. assert (subspec (F A) (Step (T F) A)) by apply H0.  
  assert (forall A, subspec ((T F) A) (T (Step (T F)) A)). (* assumption, mono of T *)
  intros;intro;intros. eapply T_mono. Focus 3. eapply H2. firstorder. firstorder.
  assert (forall A, subspec (T (Step (T F)) A) (Step (T (T F)) A)).
  intros;intro;intros. apply T_compat. apply T_mono. eauto. trivial.
  assert (forall A, subspec (Step (T (T F)) A) (Step (T F) A)). (* idempotency of T *)
  intros;intro;intros. inversion H4; subst.
  eapply Step_def. apply H5.
  intros;intro;intros. edestruct H6. apply H8. constructor. assumption.
  eapply sstep. eassumption. apply T_idem. assumption. assumption.
  assert (forall A, subspec ((T F) A) (Step (T F) A)).
  intros;intro;intros. apply H4. apply H3. apply H2. trivial.
  eapply t_gfp_help with (A:=A) in H5.
  intro;intros. apply H5. apply T_id. trivial. trivial.
Qed.
  
Lemma T_rule_f : forall F, mono F -> (forall A, subspec (F A) (t A)) ->
                           (forall A, subspec (T F A) (t A)).
Proof.
  intros;intro;intros.
  assert (forall A, subspec (T F A) (T t A)).
  intros. apply T_mono; firstorder.
  pose proof T_t.
  assert (forall A, subspec (T F A) (T (T (fun _ => bot)) A)).
  intros. 
  intro;intros. apply H2 in H4. inversion H4; subst.  
  eapply T_def. eassumption. apply H6. revert H7. apply H5. unfold respectful.
  intros;intro;intros. apply H3. revert H8. apply t_mono. trivial.
  firstorder.
  eapply T_idem in H4.
  pose proof t_T. apply H5. eassumption. trivial.
Qed.

Lemma rule_by_T : forall (F : Spec -> Spec), mono F -> 
    (forall A, subspec (F (step A)) (step (T F A))) -> (forall A, subspec (F A) (t A)).
  (* true by lemma 6.2 and fb <= b(Tf) ==> f <= B(Tf) ==> f <= Bdag f ==> f <= t *)
  intros. apply t_gfp'. apply H.
  intros. unfold subspec. intros. apply Step_def with (G := F) (F := T F). eassumption.
  apply H0. trivial.
Qed.

Definition trans (X:Spec) : Spec := fun k P => exists Q, X k Q /\ (forall k', Q k' -> X k' P).

Lemma mono_trans : mono trans.
Proof.
  destruct 2. inversion H0. econstructor; split. apply H. eassumption.
  intros. apply H. apply H2. trivial.
Qed.

Lemma trans_ok_rule : forall X, subspec (trans X) (t X).
  apply rule_by_T. apply mono_trans.
  unfold subspec. intros. destruct H as [Q [HQ H]].
  destruct HQ. specialize (H _ H0). revert H. apply step_mono. apply Tf_id.
  eapply sstep;eauto. apply Tf_idem.
  firstorder. apply T_id.
  exists Q. split. apply Tf_id;assumption. intros. specialize (H k'0 H2). apply Tf_base. assumption.
Qed.

Lemma use_trans : forall A, subspec (trans (t A)) (t A).
apply t_rule. firstorder. apply trans_ok_rule.
Qed.

Lemma use_step : forall F, mono F -> forall A, subspec (step (T F A)) (T F A).
Proof.
  unfold subspec;intros. apply Tf_idem. assumption. apply Tf_base. auto.
Qed.

Lemma tstep: forall F, mono F -> forall A x P,
    forall x', cstep x x' -> T F A x' P -> T F A x P.
Proof.
  intros. apply use_step. assumption. eapply sstep;eassumption.
Qed.
Lemma tdone: forall F, mono F -> forall A x (P:cfg->Prop), P x -> T F A x P.
Proof.
  intros. apply use_step. assumption. eapply sdone;eassumption.
Qed.

Lemma ttrans: forall F, mono F -> forall A x Q P,
    T F A x Q -> (forall y, Q y -> T F A y P) -> T F A x P.
Proof.
  intros. apply Tf_idem. assumption. apply Tf_t. assumption.
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
    (forall A, subspec (F A) (step (T F A))) ->
    (forall X, subspec X (F X) -> subspec X reaches)
    (* == subspec (gfp F) reaches *).
  intros.
  assert (forall A, subspec (F A) (t A)).
  intros. apply rule_by_T. apply H.
  unfold subspec;intros. apply H0 in H2. revert H2. apply step_mono.
  unfold subspec;intros. apply Tf_idem. assumption.
  revert H2. apply T_mono. assumption. apply Tf_base.
  apply proof_by_t. intro;intros.
  apply H1 in H3. apply H0 in H3.
  revert H3. apply step_mono. apply T_rule_f. assumption. assumption.
Qed.

End relations.

Print Assumptions ok.

