(* Properties of transition systems (relations) and
   transitive closure that do not depend on the
   axiomatization of syntax from matchingl.v *)

Set Implicit Arguments.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Setoid.

Section FixDomain.
Variable M : Set.
Definition terminates (gamma : M) (R : relation M) :=
  Acc (fun x y => R y x) gamma.

(* transitive closure. If the flag is false,
   reflexive steps are allowed as well *)
Inductive clos (A : Type) (R : A -> A -> Prop) :
  bool -> A -> A -> Prop :=
| clos_refl : forall a, clos R false a a
| clos_step : forall s a b, R a b -> clos R s a b
| clos_trans : forall s a b c,
  clos R s a b -> clos R s b c -> clos R s a c.

Definition clos_unstrict A (R : relation A) a b
  (step : clos R true a b) : clos R false a b.
Proof. induction step; eauto using clos. Defined.

Inductive clos_left (A : Type) (R : A -> A -> Prop) :
  bool -> A -> A -> Prop :=
| clos_left_refl : forall a, clos_left R false a a
| clos_left_step : forall s a b, R a b -> clos_left R s a b
| clos_left_ext : forall s a b c,
  R a b -> clos_left R s b c -> clos_left R s a c.

Lemma clos_left_trans (A : Type) (R : A -> A -> Prop)
  strict a b c :
  clos_left R strict a b -> clos_left R strict b c ->
  clos_left R strict a c.
induction 1.
auto.
apply clos_left_ext. assumption.
intros. specialize (IHclos_left H1).
eapply clos_left_ext; eassumption.
Qed.

Lemma clos_iff_left (A : Type) (R : A -> A -> Prop)
  strict a b : clos R strict a b <-> clos_left R strict a b.
Proof.
split.
induction 1.
constructor.
constructor;assumption.
eapply clos_left_trans;eassumption.

induction 1.
constructor.
constructor;assumption.
eauto using clos.
Qed.

Lemma clos_cons_lt A (R : relation A) a b s c :
  clos R true a b -> clos R s b c -> clos R true a c.
Proof. induction 2;eauto using clos. Qed.

Lemma clos_trans_lt A (R : relation A) a b s c :
  clos R s a b -> clos R false b c -> clos R s a c.
Proof. destruct s; eauto using clos_cons_lt, clos. Qed.

Lemma clos_cons_rt A (R : relation A) a s b c :
  clos R s a b -> clos R true b c -> clos R true a c.
Proof. induction 1;eauto using clos. Qed.

Lemma clos_cat A (R : relation A) a s1 b s2 c :
  clos R s1 a b -> clos R s2 b c -> clos R (orb s1 s2) a c.
Proof.
destruct s1. apply clos_cons_lt.
destruct s2. apply clos_cons_rt.
apply clos_trans.
Qed.

Lemma terminates_fwd (R : relation M) (gamma : M) :
  terminates gamma R ->
  forall strict gamma', clos R strict gamma gamma' ->
    terminates gamma' R.
Proof.
  intros.
  induction H0.
  assumption.
  destruct H. apply H. assumption.
  auto.
Qed.

Lemma terminates_trans (R : relation M) (gamma : M) :
  terminates gamma R -> terminates gamma (clos R true).
Proof.
  induction 1.
  constructor.
  intros.
  rewrite clos_iff_left in H1.
  remember true as strict; destruct H1.
  discriminate.
  subst s.
  apply H0. assumption.
  apply terminates_fwd with b true.
  apply H0. assumption.
  rewrite <- clos_iff_left in H2.
  subst.
  constructor. assumption.
Qed.

Lemma clos_weaken (A : Type) (R1 R2 : relation A) strict x y :
  (forall a b, R1 a b -> R2 a b) ->
  clos R1 strict x y -> clos R2 strict x y.
Proof. induction 2; eauto using clos. Defined.

(* Could be loosened to only require the weakening
   for values under x *)
Lemma Acc_weaken A (R1 R2 : relation A)
  (HWeak : forall a b, R2 a b -> R1 a b)
  (x : A) : Acc R1 x -> Acc R2 x.
Proof. induction 1; constructor; auto. Qed.

End FixDomain.