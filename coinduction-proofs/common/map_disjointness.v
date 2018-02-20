Require Import Setoid.
Require Import Morphisms.

Require Import maps.
Require Import sets.

Set Implicit Arguments.

Inductive InSet (Elt : Type) (v : Elt) : MultiSet Elt -> Prop :=
| in_item : InSet v (setItem v)
| in_join_l : forall l r, InSet v l -> InSet v (setJoin l r)
| in_join_r : forall l r, InSet v r -> InSet v (setJoin l r)
.

Lemma in_equiv {Elt} (v : Elt) s1 s2 :
  SetEquiv s1 s2 -> (InSet v s1 <-> InSet v s2).
induction 1;split;try solve[auto using InSet | firstorder];intro;
repeat match goal with
| [H : InSet _ (setJoin _ _) |- _] =>
  inversion H;clear H;subst
| [H : InSet _ setEmpty |- _] =>
  solve[inversion H]
end;
firstorder;eauto using InSet.
Qed.

Lemma in_split (Elt : Type) (v : Elt) (m1 m2 : MultiSet Elt) :
  InSet v (setJoin m1 m2) <-> (InSet v m1 \/ InSet v m2).
split;inversion 1;subst;auto using InSet.
Qed.

Fixpoint disjointFrom {Elt} (s : MultiSet Elt) (used : MultiSet Elt) : Prop :=
match s with
| setEmpty => True
| setItem v => ~InSet v used
| setJoin l r => disjointFrom l (setJoin r used) /\ disjointFrom r (setJoin l used)
end.

Lemma disjointSplit {Elt} (s : MultiSet Elt) :
  forall (u1 u2 : MultiSet Elt),
  disjointFrom s (setJoin u1 u2) <->
  (disjointFrom s u1 /\ disjointFrom s u2).
induction s.
* tauto.
* simpl.
  split.
  intro H;split;contradict H;auto using InSet.
  destruct 1. inversion 1;subst;tauto.
* simpl. intros. rewrite !IHs1, !IHs2. tauto.
Qed.

Lemma disjointItem {Elt} (s : MultiSet Elt) :
  forall (v : Elt),
  (disjointFrom s (setItem v) <-> ((~ InSet v s) /\ disjointFrom s setEmpty)).
induction s.
simpl. firstorder. inversion 1.
simpl. firstorder;contradict H;inversion H;congruence.
simpl. intro.
 rewrite !disjointSplit.
    rewrite IHs1. rewrite IHs2. clear IHs1 IHs2.
   intuition (eauto using InSet). inversion H3;subst;tauto.
Qed.

Lemma disjointUsedEquiv {Elt} (s : MultiSet Elt) :
  Proper (SetEquiv ==> iff) (disjointFrom s).
unfold Proper, respectful;simpl.
induction s;simpl.
reflexivity.
intros. rewrite (in_equiv e H). reflexivity.
intros.
rewrite IHs1;[
  rewrite IHs2;[
  | rewrite H]
|rewrite H];reflexivity.
Qed.

Lemma andL : forall P, P /\ True <-> P.
firstorder.
Qed.
Lemma andComm : forall P Q, P /\ Q <-> Q /\ P.
firstorder.
Qed.

Add Parametric Morphism E : (@InSet E) with
  signature eq ==> SetEquiv ==> iff as in_set_mor.
Proof. apply in_equiv. Qed.

Add Parametric Morphism E : (@disjointFrom E) with
  signature SetEquiv ==> SetEquiv ==> iff as disjoint_from_mor.
Proof.
induction 1;simpl;intros.
* rewrite andL. apply disjointUsedEquiv.
  rewrite equivComm. rewrite equivUnit. assumption.
* do 2 match goal with
  | [|- context [disjointFrom ?s (setJoin ?t x0)]] =>
    setoid_replace (disjointFrom s (setJoin t x0))
    with (disjointFrom s (setJoin t y0))
    ;[|apply disjointUsedEquiv;rewrite H0;reflexivity]
  end. tauto.
* setoid_replace (disjointFrom s1 (setJoin s2 (setJoin s3 x0)))
            with (disjointFrom s1 (setJoin (setJoin s2 s3) y0));
   [|apply disjointUsedEquiv;rewrite H0;rewrite equivAssoc;reflexivity].
  setoid_replace (disjointFrom s2 (setJoin s1 (setJoin s3 x0)))
            with (disjointFrom s2 (setJoin s3 (setJoin s1 y0)));
   [|apply disjointUsedEquiv;rewrite H0;
            rewrite <- equivAssoc;rewrite (equivComm s1);apply equivAssoc].
  setoid_replace (disjointFrom s3 (setJoin (setJoin s1 s2) x0))
            with (disjointFrom s3 (setJoin s2 (setJoin s1 y0)));
   [|apply disjointUsedEquiv;rewrite H0;rewrite (equivComm s1);apply equivAssoc].
  tauto.
* rewrite IHSetEquiv1.  
  rewrite IHSetEquiv2. reflexivity.
  apply set_join_mor;assumption.
  apply set_join_mor;assumption.
* rewrite IHSetEquiv1. apply IHSetEquiv2.
  eassumption. reflexivity.
* rewrite IHSetEquiv. reflexivity. symmetry. assumption.
* apply disjointUsedEquiv. assumption.
Qed.

Definition wfMap {Key Elt : Type} (m : Map Key Elt) : Prop :=
  disjointFrom (keys m) setEmpty.

Lemma disjointGrow {Elt : Type} (m s1 s2 : MultiSet Elt) :
  disjointFrom m (setJoin s1 s2) -> disjointFrom m s2.
revert s1 s2.
induction m;simpl;try tauto.
intros. contradict H. constructor(assumption).

destruct 1.
rewrite equivCommAssoc in H, H0.
firstorder.
Qed.

Lemma disjointEmpty {Elt : Type} (m s : MultiSet Elt) :
  disjointFrom m s -> disjointFrom m setEmpty.
rewrite <- (equivUnit s).
apply disjointGrow.
Qed.