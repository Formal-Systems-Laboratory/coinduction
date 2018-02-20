Require Import proof.

Set Implicit Arguments.

(* x terminates / R is well-ordered under x / Acc with arguments flipped *)
Inductive Term (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
  Term_intro : (forall y : A, R x y -> Term R y) -> Term R x.

Section relations.
Variables (cfg : Set) (cstep : cfg -> cfg -> Prop).

CoInductive div_path k : Prop :=
  div_step : forall k', cstep k k' -> div_path k' -> div_path k.

(* Inductive predicate for reaching in finite time *)
Inductive ireaches (k : cfg) (P : cfg -> Prop) : Prop :=
  | idone : P k -> ireaches k P
  | istep : forall k', cstep k k' -> ireaches k' P -> ireaches k P.

Lemma reaches_terminating : forall k P, Term cstep k -> reaches cstep k P -> ireaches k P.
Proof. induction 1;destruct 1;eauto using ireaches. Qed.

Definition excluded_middle_termination x :=
  ~(forall y, cstep x y -> Term cstep y) -> exists y, cstep x y /\ ~Term cstep y.

Lemma diverging_reaches : (forall x, excluded_middle_termination x) ->
  forall k, ~Term cstep k -> forall P, reaches cstep k P.
intros H.
cofix.
intros.
destruct (H k).
contradict H0. constructor;assumption. destruct H1.
apply rstep with x.
assumption.
apply diverging_reaches. assumption.
Qed.

Definition dec_term k := Term cstep k \/ ~Term cstep k.

Lemma adequate_fwd : forall k, dec_term k -> forall P, reaches cstep k P -> ireaches k P \/ ~Term cstep k.
destruct 1;auto using reaches_terminating.
Qed.

Lemma adequate_rev : (forall k, excluded_middle_termination k) ->
         forall k P, ireaches k P \/ ~Term cstep k -> reaches cstep k P.
destruct 2.
induction H0;eauto using reaches.
auto using diverging_reaches.
Qed.
End relations.