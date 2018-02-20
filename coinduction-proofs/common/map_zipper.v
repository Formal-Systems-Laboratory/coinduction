Require Import maps.
Set Implicit Arguments.
Set Contextual Implicit.

Inductive MapRep (Key Elt : Type) : Type :=
   rEmpty : MapRep Key Elt
 | rItem : Key -> Elt -> MapRep Key Elt
 | rJoin : MapRep Key Elt -> MapRep Key Elt -> MapRep Key Elt
 | rLeaf : Map Key Elt -> MapRep Key Elt
 .

Function join {Key Elt} (m1 m2 : Map Key Elt) : Map Key Elt :=
  match m1, m2 with
    | mapEmpty, _ => m2
    | _, mapEmpty => m1
    | _, _ => m1 :* m2
  end.
Lemma join_sem : forall {K E} (m1 m2 : Map K E), m1 :* m2 ~= join m1 m2.
Proof.
intros. functional induction (join m1 m2).
apply equivUnitL.
apply equivUnit.
apply equivRefl.
Qed.

Fixpoint unrep {K E} (r : MapRep K E) : Map K E :=
  match r with
    | rEmpty => mapEmpty
    | rItem k v => k |-> v
    | rJoin l r => unrep l :* unrep r
    | rLeaf m => m
  end.
Fixpoint simplRep {K E} (r : MapRep K E) : Map K E :=
  match r with
    | rEmpty => mapEmpty
    | rItem k v => k |-> v
    | rJoin l r => join (simplRep l) (simplRep r)
    | rLeaf m => m
  end.

Lemma simplValid {K E} (r : MapRep K E) : unrep r ~= simplRep r.
induction r;try reflexivity.
simpl. rewrite <- join_sem. apply equivJoin;assumption.
Qed.

Inductive MapZipper (Key Elt : Type) : Type :=
   Here : MapZipper Key Elt
 | Left : forall {r : Map Key Elt}, MapZipper Key Elt -> MapZipper Key Elt
 | Right : forall {l : Map Key Elt}, MapZipper Key Elt -> MapZipper Key Elt
 .

Fixpoint plug {K E} (z : MapZipper K E) (m : Map K E) : Map K E :=
  match z with
    | Here => m
    | Left r z' => plug z' m :* r
    | Right l z' => l :* plug z' m
  end.

Fixpoint plug' {K E} (z : MapZipper K E) : Map K E :=
  match z with
    | Here => mapEmpty
    | Left r Here => r
    | Left r z' => plug' z' :* r
    | Right l Here => l
    | Right l z' => l :* plug' z'
  end.

Lemma plug'_plug : forall {K E} (z : MapZipper K E), plug' z ~= plug z mapEmpty.
intros. induction z;simpl;
[reflexivity|..];rewrite <- IHz; clear IHz;
(destruct z;[simpl;rewrite ?equivUnit,?equivUnitL|..];reflexivity).
Qed.

Lemma plug_plug' : forall {K E} m (z : MapZipper K E), plug z m ~= m :* plug' z.
induction z;simpl;
[rewrite equivUnit;reflexivity|..];
rewrite IHz;clear IHz.

rewrite equivAssoc. destruct z;[simpl;rewrite equivUnitL|..];reflexivity.
destruct z;rewrite equivComAssoc;[simpl;rewrite equivUnit|..];reflexivity.
Qed.

Lemma same_item {K E} k v m' (z : MapZipper K E):
   plug' z ~= m' -> plug z (k |-> v) ~= k |-> v :* m'.
intros. rewrite <- H. apply plug_plug'.
Qed.

Lemma equiv_item {K E} k v v' m' (z : MapZipper K E):
   v = v' -> plug' z ~= m' -> plug z (k |-> v) ~= k |-> v' :* m'.
intros. subst. rewrite <- H0. apply plug_plug'.
Qed.

Lemma item_test : forall (k1 k2 : nat) (v1 v2 : nat) (m1 : Map nat nat),
    exists m1',
    exists v2',
    k1 |-> v1 :* m1 :* k2 |-> v2 ~= k2 |-> v2' :* k1 |-> v1 :* m1'.
intros. eexists. eexists.
refine (equiv_item (Right (Right Here)) (eq_refl _) _);unfold plug'.
refine (equiv_item (Left Here) (eq_refl _) _);unfold plug'.
reflexivity.
Qed.

Ltac find k m s :=
  match m with
    | @mapItem ?K ?E k _ => let t := constr:(@Here K E) in s t
    | ?l :* ?r =>
         find k l ltac:(fun m => let m' := constr:(Left (r:=r)  m) in s m')
      || find k r ltac:(fun m => let m' := constr:(Right (l:=l) m) in s m')
  end.
Ltac items := 
  match goal with
  |[|- ?m ~= ?k |-> _ :* _] =>
    find k m ltac:(fun t => (apply (same_item t) || apply (equiv_item t));
                             [..|unfold plug';instantiate;items])
  |_ => idtac
  end.

Lemma item_tac_test : forall (k1 k2 k3 : nat) (v1 v2 : nat) (m1 : Map nat nat),
    exists v1', exists v2', exists v3',
    k3 |-> v1 :* k1 |-> v1 :* k2 |-> v1 ~= k2 |-> v2' :* k1 |-> v1' :* k3 |-> v3'.
intros; repeat eexists.
items. apply equivRefl.
Qed.
Print item_tac_test.