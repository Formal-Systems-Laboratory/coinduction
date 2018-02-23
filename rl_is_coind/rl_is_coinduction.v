Require Import proofsystem.
Require Import coinduction.

Section Semantics.

  Parameter cfg : Set.
  Parameter R : cfg -> cfg -> Prop.

  Definition claims_of_rule (env:Type) (l r : formula cfg env) (x : cfg) (P : cfg -> Prop) : Prop :=
     exists e, l e x /\ (forall x', r e x' -> P x').
  Definition claims_of_system (rules : system cfg) (x : cfg) (P : cfg -> Prop) : Prop :=
    exists (env:Type) l r, rules env l r /\ claims_of_rule env l r x P.
  Definition claims_of_opt_system (rules : option (system cfg)) : Spec cfg :=
    match rules with
    | Some actual_rules => claims_of_system actual_rules
    | None => fun x P => False
    end.

Definition interp (C : option (system cfg)) (A : system cfg)
           env (l r : formula cfg env) (X : Spec cfg) : Prop :=
  forall x P, claims_of_rule env l r x P ->
              step R (trans R X) x P.

Ltac assert_arg H :=
  match type of H with
  | ?T -> _ => let HT := fresh "HT" in assert T as HT;[|specialize (H HT);clear HT]
  end.

Lemma rl_to_coinduction: forall C A env (l r : formula cfg env) (X : Spec cfg)
    (H_A: forall x P, claims_of_system A x P ->
           (match C with None => reaches R x P \/ X x P
                       | Some _ => next R (reaches R) x P end))
    (H_C: forall x P, claims_of_opt_system C x P -> X x P),
    IS cfg R C A env l r ->
    forall x P, claims_of_rule env l r x P ->
    match C with
      | None => trans R X x P
      | Some _ => next R (trans R X) x P
    end.
Proof.
  intros until 2;induction 1;destruct 1 as (rho & ? & ?);
        repeat match goal with | [H : _ |- _] => specialize (H H_A H_C) end.
  + (* is_step *)
    destruct (H _ _ H0) as [[]].
    assert (P x0) by auto.
    destruct C;eauto using next, trans.
  + (* is_axiom *)
    intros.
    specialize (H_A x P).
    assert_arg H_A.
    do 7 (eassumption || esplit).
    destruct C;destruct H_A;eauto using next,trans.
  + (* is_refl *)
    destruct C;[destruct H|auto using ddone].
  + (* is_trans *)
    clear H H0.
    specialize (IHIS1 x (phi' rho)).
    assert_arg IHIS1.
    eexists;esplit;[eassumption|]. trivial.
    assert_arg IHIS2.
      clear -H_A H_C.
      intros.
      destruct H as (? & ? & ? & ? & ?).
      assert (A x0 x1 x2 -> reaches R x P \/ X x P) by
        (clear H;intros;specialize (H_A x P);
            assert_arg H_A;[solve[repeat (eassumption || esplit)]|
         destruct C;destruct H_A;eauto using reaches]).
      destruct C as [C|];[|solve[auto]].
      destruct H;[|solve[auto]].
      clear H1.
      right. apply H_C. simpl. repeat (eassumption || esplit).
    assert_arg IHIS2;[solve[destruct 1]|].
    destruct C as [C | ].
    - (* C is Some -> this is the interesting case *)
    destruct IHIS1. econstructor;[eassumption|].
    eapply dtrans';[eassumption|].
    intros. apply IHIS2.
    repeat (eassumption || esplit).
    - (* C is None *)
    eapply dtrans';[eassumption|].
    intros. apply IHIS2.
    repeat (eassumption || esplit).
  + (* is_conseq *)
    apply H in H2. clear H.
    apply IHIS.
    repeat (eassumption || esplit).
    eauto.
  + (* is_case *)
    destruct H1.
    apply IHIS1;repeat (eassumption || esplit).
    apply IHIS2;repeat (eassumption || esplit).
  + (* is_abstr *)
    destruct H0.
    apply IHIS.
    repeat (eassumption || esplit).
  + (* is_abstr' *)
    apply IHIS.
    destruct H1.
    specialize (H rho x0).
    repeat (eassumption || esplit).
    intros. specialize (H x'). destruct H.
    eauto.
  + (* is_circ *)
    admit. (* not allowed in set circularity proofs *)
  + (* is_subst *)
    apply IHIS.
    repeat (eassumption || esplit).
  + (* is_lf *)
    apply IHIS.
    destruct H0.
    repeat (eassumption || esplit).
    eauto.
Admitted.

Theorem rl_is_coinduction: forall C A env (l r : formula cfg env)
    (H_A: forall x P, claims_of_system A x P -> next R (reaches R) x P),
    IS cfg R (Some C) A env l r ->
    forall x P, claims_of_rule env l r x P -> step R (trans R (claims_of_system C)) x P.
Proof.
intro C; intros.
cut (next R (trans R (claims_of_system C)) x P).
clear. destruct 1;eauto using step.
eapply rl_to_coinduction with (C:=Some C) (X:=claims_of_system C);
try eassumption.
trivial.
Qed.

Require generic_ex.
Import reduction.

Section TerminationLEM.
(* Because the soundness proof mentions termination in various definitions,
   to show equivalence with our definitions in Coq's constructive logic
   we need to assume excluded middle for termination.
 *)
  Parameter term_EM: forall x, terminates x R \/ ~terminates x R.

  Parameter term_next_EM: forall x,
           (exists x', R x x' /\ ~ terminates x' R)
      \/ ~ (exists x', R x x' /\ ~ terminates x' R).

  CoInductive diverges x : Prop :=
    d_step : forall x', R x x' -> diverges x' -> diverges x.

  Lemma nonterm_diverges : forall x, ~terminates x R -> diverges x.
    cofix.
    intros.
    destruct (term_next_EM x).
    destruct H0 as (x' & Hstep & Hx').
    * apply (d_step _ x' Hstep). apply nonterm_diverges. assumption.
    * contradict H. constructor.
      intros. fold (terminates y R).
      destruct (term_EM y). assumption.
      contradict H0. exists y. split;assumption.
  Qed.

  Lemma diverge_reaches : forall x, diverges x -> forall P, reaches R x P.
    intros. revert x H. cofix.
    destruct 1. apply (rstep H). apply diverge_reaches;assumption.
  Qed.

  Lemma clos_reaches : forall b x x', clos R b x x' -> forall (P : cfg -> Prop), P x' -> reaches R x P.
    intros. apply clos_iff_left in H.
    revert x H. induction 1;eauto using reaches.
  Qed.

  Lemma term_reaches_clos : forall x P, terminates x R -> reaches R x P
                                        -> exists x', P x' /\ clos R false x x'.
    induction 1;destruct 1.
    exists x. split. assumption. constructor.
    specialize (H0 _ H1 H2).
    destruct H0 as (x' & Hx' & Hpath).
    exists x'. split. assumption. eauto using clos.
  Qed.

  Lemma rule_faithfulness:
  forall b env (l r : formula cfg env),
    ((generic_ex.holds R b l r)
     <-> (forall x P, claims_of_rule _ l r x P -> (if b then next R else id) (reaches R) x P)).
  unfold generic_ex.holds, claims_of_rule. split;intros.
  * (* forward direction *)
    destruct H0 as (e & ? & ?).
    specialize (H e x).
    destruct (term_EM x).
    + (* terminates *) specialize (H H2 H0). destruct H as (gamma' & Hr & Hpath).
    apply H1 in Hr.
    destruct b.
    apply clos_iff_left in Hpath.
    inversion Hpath;subst;(econstructor;[eassumption|]).
      eauto using reaches.
      apply clos_iff_left in H3. eauto using clos_reaches.
    unfold id;simpl. eauto using clos_reaches.
    + (* diverges *)
      clear -H2.
      apply nonterm_diverges in H2. destruct H2.
      destruct b;(econstructor;[eassumption|]);auto using diverge_reaches.
  * (* reverse direction *)
    specialize (H gamma (r rho)).
    lapply H;[|solve[eauto]].
    intros.
    destruct b.
    - destruct H2.
      apply term_reaches_clos in H3.
      destruct H3 as (gamma' & Hgamma' & Hpath).
      exists gamma'. split. assumption.
        eapply clos_cons_lt;eauto using clos.
        destruct H0. apply H0. assumption.
    - unfold id in H2.
      apply term_reaches_clos in H2. assumption.
      assumption.
  Qed.

  Theorem system_faithfulness:
  forall A, generic_ex.system_holds R A
            <-> (forall x P, claims_of_system A x P -> next R (reaches R) x P).
    unfold generic_ex.system_holds, claims_of_system.
    split;intros.
    *
      destruct H0 as (env & l & r & Hrule & ?).
      specialize (H _ _ _ Hrule).
      pose proof (proj1 (rule_faithfulness true env l r)).
      specialize (H1 H). auto.
    *
      apply rule_faithfulness. intros.
      apply H;clear H. eauto.
  Qed.

End TerminationLEM.
End Semantics.
