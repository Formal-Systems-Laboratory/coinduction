Module Type preorder.
Parameter (X : Set) (le : X -> X -> Prop).
Axiom (le_refl : forall x, le x x).
Axiom (le_trans : forall x y z, le x y -> le y z -> le x z).
Parameter (join : X -> X -> X).
Axiom (join_l : forall x' x y, le x' x -> le x' (join x y)).
Axiom (join_r : forall y' x y, le y' y -> le y' (join x y)).
Axiom (join_u : forall x y z, le x z -> le y z -> le (join x y) z).

Definition monotone (f : X -> X) :=
  forall x y, le x y -> le (f x) (f y).
Definition closure (f : X -> X) :=
  monotone f /\ (forall x, le x (f x)) /\ (forall x, le (f (f x)) (f x)).

Parameter (lfp : (X -> X) -> X).
Parameter (lfp_fixed : forall f (H : monotone f), f (lfp f) = lfp f).
Parameter (lfp_least : forall f (H : monotone f) x, le (f x) x -> le (lfp f) x).

End preorder.

Module closure_props (P : preorder).

Import P.

Create HintDb order_hints.
Local Hint Resolve le_refl le_trans join_l join_r join_u : order_hints.

Local Hint Extern 2 (le ?l (lfp ?f)) => (replace (le l (lfp f)) with (le l (f (lfp f)))
  by (apply f_equal; apply (lfp_fixed f); solve[auto])) : order_hints.

Local Hint Resolve lfp_least : order_hints.

Definition least_closure (f : X -> X) (x : X) : X :=
  lfp (fun Y => join (f Y) x).

Lemma closure_base : forall f, monotone f -> forall x, monotone (fun Y => join (f Y) x).
unfold monotone;intros. auto with order_hints.
Qed.

Require Import Setoid.

Lemma clomon : forall f, monotone f -> monotone (least_closure f).
intros. pose proof (closure_base _ H). unfold least_closure.
intro; auto with order_hints.
Qed.

Lemma closoure_closed : forall f, monotone f -> closure (least_closure f).
intros. pose proof (closure_base _ H). unfold least_closure.
split;[|split];
intro;auto with order_hints.
Qed.

Lemma closure_above : forall f, monotone f -> forall x, le (f x) (least_closure f x).
intros. pose proof (closure_base _ H). unfold least_closure.
auto 12 with order_hints.
Qed.

Lemma closure_least : forall f, monotone f -> forall c, closure c ->
      (forall x, le (f x) (c x)) -> (forall x, le (least_closure f x) (c x)).
intros. pose proof (closure_base _ H). unfold least_closure.
destruct H0 as (? & ? & ?).
eauto with order_hints.
Qed.

End closure_props.

Print closure_props.