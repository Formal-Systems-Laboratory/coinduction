Require Import cotrans_derived.

Set Implicit Arguments.

Module HoFixpoints(L : language).

Module C := Cotrans L.
Import L.
Import C.

(* least and greatest fixpoints.
Ideally we could define them like
CoInductive gfp ... := Gfp : subrel (F (gfp F)) (gfp F)
Inductive lfp ...   := Lfp : subrel (F (lfp F)) (lfp F)
but Coq's "positivity condition" does not allow a (co)inductive type
to occur on the left-hand-side of the subrel like that.
Instead we rely on the impredicativity of prop to use the simple set-theoretic definitions.
*)

(* The greatest fixpoint is defined as the union of F-stable sets *)
Inductive gfp (F : RRel -> RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  Gfp : forall X, (subrel X (F X)) -> X x P -> gfp F x P.
Lemma gfp_unfold : forall F, mono F -> subrel (gfp F) (F (gfp F)).
Proof. destruct 2. apply H0 in H1. revert H1. apply H. firstorder. Qed.
Lemma gfp_fold : forall F, mono F -> subrel (F (gfp F)) (gfp F).
Proof. unfold subrel;eauto using gfp, gfp_unfold. Qed.
Lemma gfp_greatest : forall F, mono F -> forall X, subrel X (F X) -> subrel X (gfp F).
Proof. unfold subrel; eauto using Gfp. Qed.


(* The least fixpoint is defined as the intersection of F-closed sets *)
Inductive lfp (F : RRel -> RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  Lfp : (forall X, subrel (F X) X -> X x P) -> lfp F x P.
Lemma lfp_least : forall F X, subrel (F X) X -> subrel (lfp F) X.
Proof. induction 2. firstorder. Qed.
Lemma lfp_fold : forall F, mono F -> subrel (F (lfp F)) (lfp F).
Proof. constructor. intros. apply H1. eapply H;[apply lfp_least|];eauto. Qed.
Lemma lfp_unfold : forall F, mono F -> subrel (lfp F) (F (lfp F)).
Proof. induction 2. apply H0. auto using lfp_fold. Qed.

Lemma lfp_roll : forall F G, mono F -> mono G ->
  subrel
    (lfp (fun A => F (G A)))
    (F (lfp (fun A => G (F A)))).
intros.
apply lfp_least. apply H.
apply (@lfp_fold (fun A => G (F A))).
unfold mono;auto with subrel.
Qed.

Lemma lfp_pointwise : forall F G, mono F -> mono G ->
  (forall X, subrel (F X) (G X)) ->
  subrel (lfp F) (lfp G).
intros.
apply lfp_least.
apply (subrel_trans (H1 _)).
apply lfp_fold.
assumption.
Qed.

(* Combining rules *)
Definition union_rrel (R1 R2 : RRel) : RRel :=
  fun x P => R1 x P \/ R2 x P.
Lemma union_rrel_l (R1 R2: RRel) : subrel R1 (union_rrel R1 R2).
firstorder.
Qed.
Lemma union_rrel_r (R1 R2: RRel) : subrel R2 (union_rrel R1 R2).
firstorder.
Qed.

(* Is this conclusion in a nice usable form?
   Probably the complete higher-order spec for a program
   would include some non higher-order claims about e.g. the
   main entry point, which would thus be in
   Spec N P for any N and P, so the final conclusion here
   could be useful after all.

   Still, can we knock it around enough to get
   subrel (Spec reaches reaches) reaches?
 *)
Lemma higher_order_stability
   (* spec with positive and negative terms *)
   (Spec : RRel -> RRel -> RRel)
   (Spec_mono : forall X Y, subrel X Y -> forall A, subrel (Spec A X) (Spec A Y))
   (Spec_anti : forall A B, subrel A B -> forall X, subrel (Spec B X) (Spec A X))
   (F : RRel -> RRel)
   (F_valid : derived_valid_m F)
   (F_sound : forall Claims, subrel Claims (stepF (derived F Claims)) -> sound Claims)
   (H_proof :
     forall (Neg Pos : RRel)
       (Neg_ev : subrel (derived F (Spec Neg Pos)) Neg)
       (Pos_ev : subrel Pos (derived F (Spec Neg Pos))),
       subrel (Spec Neg Pos) (stepF (derived F (Spec Neg Pos))))
   : let N := union_rrel reaches (lfp (fun A => derived F (Spec reaches A)))
     in subrel (lfp (fun A => Spec N (derived F A))) reaches.
intro N.
pose (P := lfp (fun A => derived F (Spec N A))).
specialize (H_proof N P).
assert (subrel P (derived F (Spec N P))) by
  (apply lfp_unfold;unfold mono;auto using deri_mono).
assert (subrel (derived F (Spec N P)) N).
apply subrel_trans with (lfp (fun A => derived F (Spec reaches A)));
  [|apply union_rrel_r].
apply subrel_trans with P.
change (subrel ((fun A => derived F (Spec N A)) P) P).
apply lfp_fold. unfold mono;auto with subrel.
apply lfp_pointwise. unfold mono;auto with subrel.
unfold mono;auto with subrel.
intros. apply deri_mono. apply Spec_anti.
apply union_rrel_l.

specialize (H_proof H0 H);clear H0 H.
apply subrel_trans with (Spec N P);
  [|apply F_sound;assumption].

apply subrel_trans with
  (Spec N (lfp (fun A => derived F (Spec N A)))).
(* this is shifting a fixpoint of a function composition *)
apply lfp_roll. clear -Spec_mono. unfold mono. auto.
unfold mono;auto with subrel.
auto with subrel.
Qed.

(* Have found, in ho_pred.v, that we may need to assume
   this kind of weakenability of relations to
   get the monotonicity properties above.
   So, check that the proof goes still through *)
Definition weakenable (R : RRel) : Prop :=
  forall (P Q : cfg -> Prop), (forall x, P x -> Q x) ->
     forall x, (R x P -> R x Q).
Lemma union_weak (X Y : RRel) :
  weakenable X -> weakenable Y -> weakenable (union_rrel X Y).
intros. unfold weakenable; intros. destruct H2;[left|right];eauto.
Qed.
Lemma reach_weak : weakenable reaches.
unfold weakenable;cofix.
intros.
destruct H0.
clear reach_weak; apply Done;auto.
apply (Step H0).
apply reach_weak with P;clear reach_weak. assumption. assumption.
Qed.

Definition weakenize (R : RRel) : RRel :=
  fun x P => exists Q, R x Q /\ (forall x, Q x -> P x).
Lemma weakenize_mono : forall (S T : RRel),
  subrel S T -> subrel (weakenize S) (weakenize T).
intros. unfold subrel, weakenize.
  destruct 1.
  exists x0. intuition.
Qed.

(*
Perhaps doesn't hold in general?
I think at least we should have something like
  lfp (F . weaken) = weaken (lfp F),
  but I don't know how to prove that either

Lemma lfp_weak : forall (F : RRel -> RRel)
   (F_mono : forall X Y, subrel X Y -> subrel (F X) (F Y))
   (F_adj_weak : forall X Y,
       (forall (P Q : cfg -> Prop),
       weakenable X -> weakenable (F X)),
   weakenable (lfp F).
*)

Definition subpred (P Q : cfg -> Prop) : Prop :=
  forall x, P x -> Q x.

Definition weak_subrel (X Y : RRel) : Prop :=
  forall (P Q : cfg -> Prop),
    subpred P Q -> forall x, X x P -> Y x Q.

Lemma subrel_from_weak (X Y : RRel) :
  weak_subrel X Y -> subrel X Y.
firstorder.
Qed.

Require Import Setoid.
Require Import Morphisms.

Definition adj_weak (F : RRel -> RRel) : Prop :=
  Proper (weak_subrel ++> weak_subrel) F.
Definition mixed_weak (F : RRel -> RRel -> RRel) : Prop :=
  Proper (weak_subrel --> weak_subrel ++> weak_subrel) F.

Lemma mixed_adj : forall F, mixed_weak F -> (forall A, weakenable A -> adj_weak (F A)).
intros.
specialize (H A A H0).
exact H.
Qed.

Lemma adj_weakens (F : RRel -> RRel) :
  adj_weak F -> forall X, weakenable X -> weakenable (F X).
firstorder.
Qed.

Lemma adj_comp (F G : RRel -> RRel) :
  adj_weak F -> adj_weak G -> adj_weak (fun A => F (G A)).
unfold adj_weak, Proper, respectful. auto.
Qed.

Lemma adj_union (F G : RRel -> RRel) :
  adj_weak F -> adj_weak G -> adj_weak (fun A => union_rrel (F A) (G A)).
intros. unfold adj_weak, Proper, respectful;intros. unfold weak_subrel;intros.
destruct H3;[left|right];firstorder.
Qed.


Definition weakenize' (R : RRel) (x : cfg) (P : cfg -> Prop) :=
  (forall Q, subpred P Q -> R x Q).

Lemma weakenize'_subrel : forall F G, (weak_subrel ==> weak_subrel)%signature F G ->
  forall X, subrel (G X) X -> subrel (F (weakenize' X)) (weakenize' X).
Proof. intros;unfold subrel;intros;unfold weakenize';intros.
apply H0. revert H1. apply H. firstorder. assumption. Qed.

Lemma lfp_weak : Proper ((weak_subrel ==> weak_subrel) ==> weak_subrel) lfp.
Proof.
intro F;intros G H.
unfold respectful in H.
unfold weak_subrel; intros.
destruct H1. constructor. intros.
eapply (H1 (weakenize' X));eauto using weakenize'_subrel.
Qed.

Lemma subrel_weak (X Y : RRel) :
  subrel X Y -> weakenable Y -> weak_subrel X Y.
firstorder.
Qed.

Lemma lfp_weak_fold (F : RRel -> RRel) :
  adj_weak F ->
  weak_subrel (F (lfp F)) (lfp F).
Proof. intros. unfold weak_subrel. intros. constructor. intros.
apply H2. revert H1. apply H;[|assumption].
unfold weak_subrel;intros. destruct H3.
eapply (H3 (weakenize' X));eauto using weakenize'_subrel.
Qed.

Lemma lfp_weak_unfold (F : RRel -> RRel) :
  adj_weak F ->
  weak_subrel (lfp F) (F (lfp F)).
Proof. unfold adj_weak;intros;unfold weak_subrel;intros. destruct H1.
eapply H;[|eassumption|].
apply lfp_weak_fold. assumption.
apply (H1 (F (F (lfp F)))).
unfold subrel. intros x0 P0. apply H. apply H.
apply lfp_weak_fold. assumption. firstorder.
Qed.

Lemma lfp_weak_unfold' (F : RRel -> RRel) :
  adj_weak F ->
  subrel (lfp F) (F (lfp F)).
unfold subrel;intros until P.
apply lfp_weak_unfold. assumption. firstorder.
Qed.

Lemma lfp_weak_least : forall F,
  adj_weak F -> forall X, weakenable X -> subrel (F X) X -> subrel (lfp F) X.
Proof. unfold subrel;intros. destruct H2;firstorder. Qed.

Lemma weak_subrel_trans : forall P Q R, weak_subrel P Q -> weak_subrel Q R -> weak_subrel P R.
unfold weak_subrel, subpred; firstorder.
Qed.

Lemma lfp_weak_pointwise : forall F G, adj_weak F -> adj_weak G ->
  (weak_subrel ++> weak_subrel)%signature F G ->
  subrel (lfp F) (lfp G).
Proof.
unfold subrel. intros until P.
apply lfp_weak. assumption. firstorder.
Qed.

Lemma lfp_shift (F G : RRel -> RRel) :
  adj_weak F -> adj_weak G ->
  subrel
    (lfp (fun A => F (G A)))
    (F (lfp (fun A => G (F A)))).
Proof.
intros.
apply lfp_weak_least.
  auto using adj_comp.
apply H; apply lfp_weak; auto using adj_comp.
intro;auto.
unfold subrel. intros x P.
apply H;[|firstorder].
match goal with
[|- context [G (F ?A)]] =>
  change (G (F A)) with ((fun A => G (F A)) A)
end.
apply lfp_weak_fold.
intro;auto.
Qed.

Definition trans (X : RRel) : RRel :=
  fun x P =>
   exists Q, X x Q /\ (forall y, Q y -> X y P).
Lemma trans_adj_weak : adj_weak trans.
unfold adj_weak, weak_subrel, subpred, Proper, respectful.
firstorder.
Qed.

Lemma deri_weak :
   Proper ((weak_subrel ==> weak_subrel) ==> (weak_subrel ==> weak_subrel)) derived.
unfold Proper,respectful;intros F G FG_adj X Y XY;unfold weak_subrel;intros P Q PQ x.
intro H. revert G FG_adj Y XY Q PQ.
induction H;try econstructor(solve[eauto]).
intros. apply drule.
eapply FG_adj;[ |eassumption..].
firstorder.
Qed.

Definition mk_weak (X : RRel) : RRel :=
  fun x Q => exists (P : cfg -> Prop),
    (forall x, P x -> Q x) /\ X x P.

Lemma weakens : forall X, weakenable (mk_weak X).
firstorder.
Qed.

Definition lift_weakenable (R : RRel -> RRel) : Prop :=
  forall X, weakenable X -> weakenable (R X).

(*
Lemma adj_from_props : forall R, lift_weakenable R -> mono R -> adj_weak R.
intros.
unfold adj_weak, ho_subrel.
intros.
(* cut through mk_weak X *)
assert (forall x P, X x P -> mk_weak X x P).
  firstorder.
unfold weak_subrel; intros.
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
*)

(* For higher order stability to go, it
  suffices to prove that when Neg and Pos are weakenable,
  N and P are as well *)

Lemma higher_order_stability'
   (* spec with positive and negative terms *)
   (Spec : RRel -> RRel -> RRel)
   (Spec_ord : mixed_weak Spec)
   (F : RRel -> RRel)
   (F_weak : adj_weak F)
   (F_valid : derived_valid_m F)
   (F_sound : forall Claims, subrel Claims (stepF (derived F Claims)) -> sound Claims)
   (H_proof :
     forall (Neg Pos : RRel)
       (W_Neg : weakenable Neg)
       (W_Pos : weakenable Pos)
       (Neg_ev : subrel (derived F (Spec Neg Pos)) Neg)
       (Pos_ev : subrel Pos (derived F (Spec Neg Pos))),
       subrel (Spec Neg Pos) (stepF (derived F (Spec Neg Pos)))) :
   let derived_lfp (Neg : RRel) : RRel :=
             lfp (fun A => derived F (Spec Neg A)) in
   let N := union_rrel reaches (derived_lfp reaches) in
   let P := derived_lfp N in
   subrel (lfp (fun A => Spec N (derived F A))) reaches.
intros.

pose proof (deri_weak F_weak).
pose proof (mixed_adj Spec_ord reach_weak).

assert (weakenable N) as N_weak.
apply union_weak. apply reach_weak. apply lfp_weak. apply adj_comp;assumption.

assert (adj_weak (Spec N)) as Spec_weak
  by (refine (Spec_ord N N N_weak)).

assert (adj_weak (fun A => derived F (Spec N A))) as comp_adj.
  apply adj_comp;assumption.

assert (weakenable P) as P_weak.
apply lfp_weak. assumption.

assert (subrel P (derived F (Spec N P))) as P_rel.
  unfold P, derived_lfp. apply lfp_weak_unfold'. assumption.

assert (subrel (derived F (Spec N P)) N) as N_rel.
apply subrel_trans with (derived_lfp reaches);
  [|apply union_rrel_r].
apply subrel_trans with P.
unfold subrel. intros x P0.
refine (lfp_weak_fold comp_adj _ _). firstorder.
(* need some arguments about monotonicity of
   derived_lfp *)
apply lfp_weak_pointwise. assumption. apply adj_comp;assumption.
clear -Spec_ord F_weak N_weak.
  unfold Proper, respectful.
  intros X Y. intros.
apply deri_weak. assumption.
apply Spec_ord.
  unfold Basics.flip, N. clear.
  unfold weak_subrel. intros. left. pose proof reach_weak. firstorder.
assumption.

specialize (H_proof N P N_weak P_weak N_rel P_rel).

apply subrel_trans with (Spec N P);
  [|apply F_sound;assumption].

(* this is shifting around a fixpoint *)
apply subrel_trans with
  (Spec N (lfp (fun A => derived F (Spec N A)))).
(* this is shifting a fixpoint of a function composition *)
apply lfp_shift. assumption. assumption.

change (subrel (Spec N P) (Spec N P)).
unfold subrel;tauto.
Qed.
End HoFixpoints.
