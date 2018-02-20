Set Implicit Arguments.

Require Import Setoid.

Parameter Base : Set.

Inductive arg_type : Set :=
 | base_arg : arg_type
 | pred_arg : pred_type -> arg_type
with pred_type : Set :=
 | pred_done : pred_type
 | pred_fun : arg_type -> pred_type -> pred_type
 | pred_neg_fun : arg_type -> pred_type -> pred_type
 .

Fixpoint arg_sem (a : arg_type) : Type :=
  match a with
  | base_arg => Base
  | pred_arg p => pred_sem p
  end
with pred_sem (p : pred_type) : Type :=
  match p with
  | pred_done => Prop
  | pred_fun a r => arg_sem a -> pred_sem r
  | pred_neg_fun a r => arg_sem a -> pred_sem r
  end.

Definition rel A := A -> A -> Prop.

Fixpoint arg_rel (a : arg_type) : rel (arg_sem a) :=
  match a with
  | base_arg => fun x y => x = y
  | pred_arg p => pred_rel_mut p
  end
with pred_rel_mut p : rel (pred_sem p) :=
  match p with
  | pred_done => fun P Q => P -> Q
  | pred_fun a r => fun P Q => forall x y, arg_rel a x y -> pred_rel_mut r (P x) (Q y)
  | pred_neg_fun a r => fun P Q => forall x y, arg_rel a y x -> pred_rel_mut r (P x) (Q y)
  end
.

Scheme arg_mut_ind := Induction for arg_type Sort Prop
with pred_mut_ind := Induction for pred_type Sort Prop.

Fixpoint pred_rel p : rel (pred_sem p) :=
  match p with
  | pred_done => fun P Q => P -> Q
  | pred_fun base_arg r => fun P Q => forall x, pred_rel r (P x) (Q x)
  | pred_neg_fun base_arg r => fun P Q => forall x, pred_rel r (P x) (Q x)
  | pred_fun (pred_arg p) r => fun P Q => forall x y, pred_rel p x y -> pred_rel r (P x) (Q y)
  | pred_neg_fun (pred_arg p) r => fun P Q => forall x y, pred_rel p y x -> pred_rel r (P x) (Q y)
  end
.

Require Import Setoid.

Lemma reps : forall p P Q, pred_rel p P Q <-> pred_rel_mut p P Q.
intro p.
induction p using pred_mut_ind
  with (P := fun a => match a with
     | base_arg => True
     | pred_arg p => forall P Q, pred_rel p P Q <-> pred_rel_mut p P Q
     end);trivial.

reflexivity.

destruct a;simpl;
repeat match goal with
 [H : forall P Q, _ <-> _ |- _] => setoid_rewrite H;clear H
end.

split;intros;subst;auto.

reflexivity.

destruct a;simpl;
repeat match goal with
 [H : forall P Q, _ <-> _ |- _] => setoid_rewrite H;clear H
end.

split;intros;subst;auto.

reflexivity.
Qed.

Definition RRel := Base -> (Base -> Prop) -> Prop.
Definition rrel_type : pred_type :=
  pred_fun base_arg (pred_fun (pred_arg (pred_fun base_arg pred_done)) pred_done).

Lemma rrel_rep : RRel = pred_sem rrel_type.
Proof. reflexivity. Defined.

Definition subrel (A B : RRel) : Prop := forall x P, A x P -> B x P.
Definition mono (F : RRel -> RRel) : Prop :=
  forall (S T : RRel), subrel S T -> subrel (F S) (F T).

Definition weakenable (R : RRel) : Prop :=
  forall (P Q : Base -> Prop), (forall x, P x -> Q x) ->
     forall x, (R x P -> R x Q).

Lemma weaken_good : forall R, weakenable R <-> pred_rel rrel_type R R.
firstorder.
Qed.

Definition adj_weak (F : RRel -> RRel) : Prop :=
  forall (X Y : RRel),
    (forall (P Q : Base -> Prop),
       (forall x, P x -> Q x) ->
       (forall x, X x P -> Y x Q)) ->
    forall (P Q : Base -> Prop),
       (forall x, P x -> Q x) ->
       forall x, F X x P -> F Y x Q.

Definition adj1 (F : RRel -> RRel) : Prop :=
  forall (X Y : RRel),
     (forall x P, X x P -> Y x P) ->
    (forall x P, F X x P -> F Y x P).
Definition adj2 (F : RRel -> RRel) : Prop :=
  forall (P Q : Base -> Prop),
    (forall x, P x -> Q x) ->
    forall (X : RRel) x, F X x P -> F X x Q.

Goal forall F, adj1 F -> adj2 F -> adj_weak F.
unfold adj1, adj2, adj_weak.
intros.
eauto.
Qed.


Lemma adj_arg :
  forall (X Y : RRel),
    (forall (P Q : Base -> Prop),
       (forall x, P x -> Q x) ->
       (forall x, X x P -> Y x Q))
    <-> pred_rel rrel_type X Y.
firstorder.
Qed.

Lemma adj_good : forall R, adj_weak R <->
  pred_rel (pred_fun (pred_arg rrel_type) rrel_type) R R.
unfold adj_weak.
setoid_rewrite adj_arg.
reflexivity.
Qed.

Definition lift_weakenable (R : RRel -> RRel) : Prop :=
  forall X, weakenable X -> weakenable (R X).

Definition lift_rrel (R : RRel -> RRel) : Prop :=
  forall (X Y : RRel),
    (forall x P, X x P -> Y x P) ->
    (forall x P, R X x P -> R Y x P).

Goal forall R, lift_rrel R <-> (forall X Y, subrel X Y -> subrel (R X) (R Y)).
firstorder.
Qed.
(* Aka, mono *)

Definition mk_weak (X : RRel) : RRel :=
  fun x Q => exists (P : Base -> Prop),
    (forall x, P x -> Q x) /\ X x P.

Lemma weakens : forall X, weakenable (mk_weak X).
firstorder.
Qed.

Lemma adj_from_props : forall R, lift_weakenable R -> lift_rrel R -> adj_weak R.
intros.
unfold adj_weak.
intros.
(* cut through mk_weak X *)
assert (forall x P, X x P -> mk_weak X x P).
  firstorder.
apply H0 in H4.
apply H4 in H3.
assert (weakenable (mk_weak X)) by apply weakens.
specialize (H _ H5 _ _ H2).
apply H in H3.
revert H3.
apply H0.
clear -H1.
firstorder.
Qed.

Goal forall R, adj_weak R -> lift_weakenable R.
firstorder.
Qed.

Goal forall R, lift_rrel R -> (lift_weakenable R <-> adj_weak R).
intros;split.
auto using adj_from_props.
firstorder.
Qed.

(*
Eval compute in pred_rel
  (pred_neg_fun (pred_arg rrel_type)
  (pred_fun (pred_arg rrel_type)
            rrel_type)).
 *)

(* adj_weak doesn't seem to imply lift_rrel *)

(*
Definition weakenable (R : (Base -> Prop) -> Base -> Prop) : Prop :=
  forall P Q, pred_rel (pred_fun base_arg pred_done) P Q ->
              pred_rel (pred_fun base_arg pred_done) (R P) (R Q).

Definition mono_rel : rel Prop := fun P Q => P -> Q.
Definition pred_rel : rel (Base -> Prop) :=
  fun P Q => forall b, mono_rel (P b) (Q b).

(P Q : Prop) : Prop := P -> Q.
Definition mono_pred (P Q : Base -> Prop) : Prop :=
  forall
 *)
