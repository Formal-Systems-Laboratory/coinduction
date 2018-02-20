Require Import maps.
Require Import patterns.

(* Various tactics for manipulating and simplifying patterns *)

Lemma exP_lift_r : forall {Key Elt A} (body : A -> MapPattern Key Elt) P,
  PatEquiv (exP body :* P) (exP (fun a => body a :* P)%pattern).
firstorder.
Qed.
Lemma exP_lift_l : forall {Key Elt A} (body : A -> MapPattern Key Elt) P,
  PatEquiv (P :* exP body) (exP (fun a => P :* body a)%pattern).
firstorder.
Qed.
Lemma exP_lift_as : forall {Key Elt A} (body : A -> MapPattern Key Elt) h,
  PatEquiv (asP h (exP body)) (exP (fun a => asP h (body a))%pattern).
firstorder.
Qed.

Create HintDb exP_lift discriminated.
Hint Rewrite @exP_lift_r @exP_lift_l @exP_lift_as : exP_lift.

(* Don't worry about the exP, just sort other stuff *)

Section pats.
Variables Key Elt : Type.

Inductive pat_skel : Type :=
  | Leaf (l : MapPattern Key Elt)
  | Empty
  | Item (k : Key) (v : Elt)
  | Lit (m : Map Key Elt)
  | Constraint (P : Prop)
  | Join (l r : pat_skel)
  .

Fixpoint close (pat : pat_skel) :=
  match pat with
    | Leaf p => p
    | Empty => emptyP
    | Item k v => itemP k v
    | Lit h => litP h
    | Constraint P => constraint P
    | Join l r => joinP (close l) (close r)
  end.

Inductive sorted : Type :=
  Sorted (constraints : list Prop)
         (items : list (Key * Elt))
         (lits : list (Map Key Elt))
         (leaves : list (MapPattern Key Elt)).

Definition merge_sorted l r :=
  match l, r with
    | Sorted l1 l2 l3 l4, Sorted r1 r2 r3 r4 =>
      Sorted (l1++r1) (l2++r2) (l3++r3) (l4++r4)
  end.

Fixpoint lift (pat : pat_skel) : sorted :=
  match pat with
    | Leaf p => Sorted  nil nil nil (p::nil)
    | Empty => Sorted nil nil nil nil
    | Item k v => Sorted nil ((k,v)::nil) nil nil
    | Lit h => Sorted nil nil (h::nil) nil
    | Constraint P => Sorted (P::nil) nil nil nil
    | Join l r => merge_sorted (lift l) (lift r)
  end.

Require Import List.
Definition rebuild (s : sorted) : MapPattern Key Elt :=
  match s with
    | Sorted constraints items lits leaves =>
      fold_right (fun P r => constraint P :* r)
        (fold_right (fun item r => itemP (fst item) (snd item) :* r)
           (fold_right (fun h r => litP h :* r)
              (fold_right (fun p r => p :* r) emptyP leaves)
            lits)
         items)
      constraints
  end%pattern.

Lemma fold_good : forall {A} (f : A -> MapPattern Key Elt) l1 l2 P1 P2 P3,
                    PatEquiv (P1 :* P2) P3 ->
  (PatEquiv (  fold_right (fun x r => f x :* r) P1 l1
            :* fold_right (fun x r => f x :* r) P2 l2)
            (fold_right (fun x r => f x :* r) P3 (l1 ++ l2)))%pattern.
intros.
induction l1.
simpl.

induction l2.
simpl. assumption.
simpl. rewrite patEquivCommAssoc, IHl2. reflexivity.

simpl.
rewrite <- IHl1, patEquivAssoc. reflexivity.
Qed.

Lemma merge_good : forall x y,
  PatEquiv (rebuild x :* rebuild y) (rebuild (merge_sorted x y)).
destruct x;destruct y;simpl.

apply fold_good.
apply fold_good.
apply fold_good.
apply fold_good.
rewrite patEquivUnit;reflexivity.
Qed.

Lemma lift_good : forall pat, PatEquiv (close pat) (rebuild (lift pat)).
induction pat;simpl;[rewrite ?patEquivUnit;reflexivity..|].
rewrite IHpat1,IHpat2.
apply merge_good.
Qed.

End pats.

(* Idea is to autorewrite with the ex-lifting base,
   then quote and rewrite to change by reflection to
   a simplified guy, then pick off stuff *)

(* A quoting tactic would be good too *)