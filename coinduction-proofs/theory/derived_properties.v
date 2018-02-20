Set Implicit Arguments.

Parameter cfg : Set.

Definition RRel : Type := cfg -> (cfg -> Prop) -> Prop.
Definition subrel (A B : RRel) : Prop := forall x P, A x P -> B x P.

Lemma subrel_trans (P Q R : RRel) :
  subrel P Q -> subrel Q R -> subrel P R.
Proof.
firstorder.
Qed.

Definition mono (F : RRel -> RRel) : Prop :=
  forall S T, subrel S T -> subrel (F S) (F T).

Parameter next : RRel -> RRel.
Parameter next_mono : mono next.

Parameter next_lift : forall (X : RRel)
  P Q (X_weakening : forall c, X c P -> X c Q),
  forall x, next X x P -> next X x Q.
(*
Parameter next_lift : forall (X Y : RRel)
  P Q (X_weakening : forall c, X c P -> Y c Q),
  forall x, next X x P -> next Y x Q.
 *)

Definition done : RRel := fun x P => P x.

Definition stepF X : RRel := fun x P => done x P \/ next X x P.

Definition stable (X : RRel) : Prop := subrel X (stepF X).

(* Using Mendler style to avoid non strictly positive occurance error in drule' *)
Inductive derivedF (F : RRel -> RRel)
                   (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dleaf : X x P -> derivedF F X x P
  | ddone : P x -> derivedF F X x P
  | dnext' : forall (Q : RRel), subrel Q (derivedF F X) ->
                       next Q x P -> derivedF F X x P
  | drule' : forall (Q : RRel), subrel Q (derivedF F X) ->
                                F Q x P -> derivedF F X x P.
Definition dnext F X x P : next (derivedF F X) x P -> derivedF F X x P :=
  dnext' (fun _ _ H => H).
Definition dstep F X x P : stepF (derivedF F X) x P -> derivedF F X x P.
  destruct 1;auto using dnext,ddone.
Qed.
Definition drule F X x P : F (derivedF F X) x P -> derivedF F X x P :=
  drule' _ _ (fun _ _ H => H).

(* show the mendler stuff can be abstracted over when splitting *)
Lemma derivedF_decompose : forall F, mono F ->
  (forall X x P, derivedF F X x P ->
    X x P \/ P x \/ next (derivedF F X) x P \/ F (derivedF F X) x P).
intros.
destruct H0; auto.
apply next_mono in H0.
auto.
apply H in H0. auto.
Qed.

Section RuleValidity.

(* Fix a set of derived rulesto show equivalence of validity properties *)
Variable F : RRel -> RRel.
Variable F_mono : mono F.

Definition proven (X : RRel) : Prop := subrel X (stepF (derivedF F X)).
Definition F_justified (X : RRel) : Prop := stable (derivedF F X).
Definition prop_m (X : RRel) : Prop :=
  subrel (F (stepF (derivedF F X))) (stepF (derivedF F X)).

Lemma justified_implies_m :forall X, F_justified X -> prop_m X.
unfold F_justified, stable, prop_m.
intros.
apply subrel_trans with (derivedF F X);[clear H|exact H].
unfold subrel; intros x P HF.
apply drule.
revert x P HF; apply F_mono.
unfold subrel; intros x P Hs.
destruct Hs. apply ddone. assumption.
apply dnext. assumption.
Qed.

Lemma proven_m_justified : forall X, prop_m X -> proven X -> F_justified X.
unfold prop_m, proven, F_justified.
intros X H HX.
unfold stable, subrel.
intros x P HD.
induction HD.
auto.
unfold stepF,done;auto.
unfold stepF;right. revert H2. apply next_mono. assumption.
apply F_mono in H1.
apply H1 in H2.
apply H in H2.
assumption.
Qed.

Definition semantically_valid : Prop :=
  forall X, proven X -> F_justified X.

Definition m_with_proof : Prop :=
  forall X, proven X -> prop_m X.

Lemma semantics_implies_m_with_proof :
  semantically_valid -> m_with_proof.
unfold semantically_valid, m_with_proof.
pose proof justified_implies_m.
auto.
Qed.

Lemma m_proof_implies_another :
  m_with_proof ->
  (forall X, proven X ->
     subrel (F X) (stepF (derivedF F X))).
unfold m_with_proof, prop_m; intros.
specialize (H _ H0).
refine (subrel_trans _ H);clear H.
apply F_mono. exact H0.
Qed.
(* Can't seem to go the other way. *)

(* Let's consider what things are strictly bigger -
   always have.
   F X <= derived F X
   what about relating F and step?
   in the end we want somthing about F (Step ...) <= Step ...
 .. assuming that x <= step (derivedF X),
   what do we get about derived F x?

  then derived F X <= derived F (step (derived F X))
    but derived F (step (derived F X)) <= derived F (derived F (derived F X)) <= derived F X.
  .. is it then fixed???
 *)

End RuleValidity.

Inductive trans (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
| Trans : forall Q, X x Q -> (forall t, Q t -> X t P) -> trans X x P.

Lemma trans_mono : mono trans.
firstorder.
Qed.

Lemma trans_valid : 
  forall X, prop_m trans X.
unfold prop_m, subrel.
destruct 1.
destruct H.
eauto using stepF.
right.
revert H.

apply next_lift.
eauto using drule,Trans,dstep.
Qed.