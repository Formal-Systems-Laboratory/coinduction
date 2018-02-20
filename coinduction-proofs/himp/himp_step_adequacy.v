Require Export ZArith.
Require Export himp_steps.
Require Export himp_syntax_sugar.
Require Import sets.
Require Import map_disjointness.
Require Import himp_claims.
Require Import himp_tactics.

Set Implicit Arguments.

Lemma kstep_resp_kequiv_fwd : forall k1 k1' k2,
  kequiv k1 k1' -> kstep k1 k2 -> (exists k2', kstep k1' k2').
Proof. intros.
destruct H0, k1'; simpl in H; decompose record H;clear H;subst;
try solve[eexists;econstructor(eassumption || reflexivity || equate_maps)];
(destruct stack as [|[]];try solve [exfalso;assumption]);
eexists;econstructor(eassumption).
Qed.

Fixpoint bounded_keys {Elt} (b : Z) (m : Map k Elt) : Prop :=
  match m with
    | mapEmpty => True
    | mapItem (kra (KInt k) kdot) _ => k < b
    | mapItem _ _ => False
    | mapJoin l r => bounded_keys b l /\ bounded_keys b r
  end.

Lemma relax_bound (b1 b2 : Z) :
  b1 <= b2 -> forall {Elt} (m : Map k Elt),
  bounded_keys b1 m -> bounded_keys b2 m.
induction m;simpl;try tauto.
destruct k; try tauto.
destruct k; try tauto.
destruct k0; try tauto.
auto with zarith.
Qed.

Lemma adjust_map (b : Z) {Elt} (m1 m2 : Map k Elt) :
  m1 ~= m2 -> (bounded_keys b m1 <-> bounded_keys b m2).
induction 1;simpl;try tauto.
Qed.

Require Import Setoid.

Add Parametric Morphism {Elt} : (@bounded_keys Elt) with
  signature Zle ==> (@MapEquiv k Elt) ==> Basics.impl as bounded_keys_mor.
unfold Basics.impl. intros.
apply (relax_bound H) in H1.
revert H1. apply adjust_map. symmetry. assumption.
Qed.

Lemma boundedness : forall {Elt}  x y (m : Map k Elt),
  InSet (kra (KInt x) kdot) (keys m) -> bounded_keys y m -> x < y.
induction m;simpl;inversion 1;subst; tauto.
Qed.

Lemma disjointness_pres : forall c c',
  kstep c c' -> (wfMap (heap c) /\ bounded_keys (alloc_mark c) (heap c))
             -> (wfMap (heap c') /\ bounded_keys (alloc_mark c') (heap c')).
(* Many rules don't mention the heap at all. *)
destruct 1;simpl;try tauto;
(* Others at least don't affect the key set,
   at worst changing a value and rearranging
   entries *)
unfold wfMap;simpl;
repeat match goal with
[H : _ ~= _ |- _] => progress rewrite H
end; try trivial;
(* Only alloc and dealloc actually change the key set
   - and most of this tactic is for Alloc, where a new key needs to be shown disjoint *)
(repeat (rewrite equivUnit);firstorder;try
repeat match goal with
 | [Hbounded : bounded_keys _ ?M |- ~ InSet _ (keys ?M) ] =>
  let HIn := fresh in intro HIn; pose proof (boundedness _ _ HIn Hbounded); solve[auto with zarith]
 | [H : bounded_keys _ ?M |- bounded_keys _ ?M ] =>
  revert H; apply relax_bound; solve[auto with zarith]
 | [|- disjointFrom _ (setItem _)] =>
   rewrite disjointItem;split
 | [H : disjointFrom ?s _ |- disjointFrom ?s setEmpty] =>
   revert H; apply disjointEmpty
end;auto).
Qed.
