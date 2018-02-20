Require Import ZArith.
Require Import List.
Require Import String.

Require Import domains.
Require Export kstep.

Open Scope k_scope.

Set Implicit Arguments.

Definition kequiv (k1 k2 : kcfg) : Prop :=
  match k1, k2 with
    | KCfg k1 store1 heap1 labels1,
      KCfg k2 store2 heap2 labels2 =>
      k1 = k2 /\ store1 ~= store2 /\ heap1 ~= heap2 /\ labels1 ~= labels2
  end.

Definition kwf (k : kcfg) : Prop :=
  match k with
  | KCfg kode store heap labels =>
     wfMap store /\ wfMap heap /\ wfMap labels
  end.

Lemma wf_pres : forall k1 k2, kwf k1 -> kstep k1 k2 -> kwf k2.
destruct 2;simpl kwf in * |- *;
  try match goal with [H : _ ~= _ |- _] => apply wf_equiv in H;simpl wfMap in H end;
  intuition (eauto using disj_item).
Qed.

Require Import Setoid.

Lemma kequiv_refl k : kequiv k k.
Proof.
destruct k;simpl;intuition reflexivity.
Qed.

Lemma kequiv_sym k1 k2 : kequiv k1 k2 -> kequiv k2 k1.
Proof.
destruct k1; destruct k2;simpl;intuition.
Qed.

Lemma kequiv_trans k1 k2 k3 : kequiv k1 k2 -> kequiv k2 k3 -> kequiv k1 k3.
Proof.
destruct k1; destruct k2; destruct k3; simpl; intuition (etransitivity; eassumption).
Qed.

Add Parametric Relation : kcfg kequiv
  reflexivity proved by kequiv_refl
  symmetry proved by kequiv_sym
  transitivity proved by kequiv_trans
  as kequiv_rel.

Create HintDb kstep_equiv_hints discriminated.
Ltac use_map_hyp :=
    match goal with
      [Heq: ?l ~= ?l', Hstruct: ?l ~= ?r |- ?l' ~= ?r'] => unify r r';
      eexact (equivTrans (equivSym Heq) Hstruct)
    end.
Hint Constructors kstep : kstep_equiv_hints.
Hint Extern 0 (kequiv _ _) =>
   split;[reflexivity|(split;[|split]);
    (assumption || apply equivRefl || use_map_hyp)]
  : kstep_equiv_hints.
Hint Resolve equivRefl : kstep_equiv_hints.
Hint Extern 3 (_ ~= _) => use_map_hyp : kstep_equiv_hints.

Lemma kstep_equiv : forall c1 c1' c2,
 kequiv c1 c1' -> kstep c1 c2 -> exists c2', kstep c1' c2' /\ kequiv c2 c2'.
intros.
destruct c1';destruct H0;unfold kequiv in H;destruct H as [<- [? [? ?]]];
try solve[eauto with kstep_equiv_hints].
Qed.