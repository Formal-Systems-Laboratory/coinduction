Require Import List.
Require Import cotrans_derived.
Require Import fixpoints.

Set Implicit Arguments.

Inductive item : Set :=
  | atom (n : nat)
  | cons (l r : item).
Inductive inst :=
  | call
  | prim (op : list item -> list item).
Inductive cfg :=
  Cfg : list inst -> list item -> cfg.

Parameter prog : nat -> option (list inst).

Inductive step : cfg -> cfg -> Prop :=
  | prim_step : forall f code stk,
                  step (Cfg (prim f :: code) stk)
                       (Cfg code (f stk))
  | prim_call : forall label env code code' stk,
                  prog label = Some code' ->
                  step (Cfg (call :: code) ((cons (atom label) env) :: stk))
                       (Cfg code' (env :: stk)).

Module CallLanguage <: language.
Definition cfg := cfg.
Definition step := step.
End CallLanguage.

Module F := HoFixpoints CallLanguage.
Import F.
Import F.C.

(*
Definition RRel : Type := cfg -> (cfg -> Prop) -> Prop.
Definition subrel (A B : RRel) : Prop := forall x P, A x P -> B x P.
Definition mono (F : RRel -> RRel) : Prop := forall A B, subrel A B -> subrel (F A) (F B).

Definition weakenable (R : RRel) : Prop :=
  forall (P Q : cfg -> Prop), (forall x, P x -> Q x) ->
     forall x, (R x P -> R x Q).

Definition weakenize (R : RRel) : RRel :=
  fun x P => exists Q, R x Q /\ (forall x, Q x -> P x).

Definition min_ext (P : RRel -> Prop) (F : RRel -> RRel) : Prop :=
  (forall R, P (F R)) /\
  (forall R, subrel R (F R)) /\
  (forall R R', subrel R R' -> P R' -> subrel (F R) R').

Lemma weakenize_good : min_ext weakenable weakenize.
repeat split;firstorder.
Qed.
 *)

Definition proprop (P : RRel -> RRel -> Prop) : Prop :=
  (forall A B, weakenable A -> weakenable B -> subrel A B ->
        (forall X, weakenable X -> P X A -> P X B)
     /\ (forall X, weakenable X -> P B X -> P A X)).

Inductive ty := num | func (a b : ty).

Fixpoint represents (i : item) (t : ty) (N P : RRel) : Prop :=
  match t with
  | num => match i with
           | atom _ => True
           | _ => False
           end
  | func t1 t2 =>
      (forall arg,
         represents arg t1 P N ->
         (forall code stk r,
           P (Cfg (call :: code) (i :: arg :: r :: stk))
             (fun cfg' =>
              match cfg' with
              | Cfg (call :: _) (r' :: v' :: stk') =>
                 r' = r /\ stk' = stk /\
                   represents v' t2 N P
              | _ => False
              end)))
  end.

Definition subweak (X Y : RRel) : Prop :=
  forall (P Q : cfg -> Prop), (forall x, P x -> Q x) -> forall x, X x P -> Y x Q.

Lemma represents_mixed : forall t (A B X Y : RRel),
  subweak A B -> subweak X Y -> forall i, represents i t B X -> represents i t A Y.

induction t;simpl;intros.
tauto.
assert (represents arg t1 X B) by
  (revert H2;apply IHt1;assumption).
specialize (H1 arg H3 code stk r).
revert H1.
apply H0.
destruct x.
destruct l;trivial.
destruct i0;trivial.
destruct l0;trivial.
destruct l0;trivial.
intuition.
revert H6.
apply IHt2;assumption.
Qed.

Lemma represents_happy : forall t i, proprop (represents i t).
unfold proprop;intros. revert i.
induction t.
unfold represents;split;trivial.
split;simpl;intros.
(* Mono in second arg *)
specialize (H3 arg).
apply IHt1 in H4;[|assumption].
specialize (H3 H4 code stk r).
apply H1 in H3.
revert H3.
(* need to weaken B here *) apply H0.
clear IHt1.
destruct x.
destruct l;[tauto|].
destruct i0;[|tauto].
destruct l0;[tauto|].
destruct l0;[tauto|].
intuition.
apply IHt2;assumption.
(* Anti-mono in first *)
specialize (H3 arg).
apply IHt1 in H4;[|assumption].
specialize (H3 H4 code stk r).
revert H3.
apply H2.
clear IHt1.
destruct x.
destruct l;[tauto|].
destruct i0;[|tauto].
destruct l0;[tauto|].
destruct l0;[tauto|].
intuition.
apply IHt2;assumption.
Qed.

Parameter id_addr : nat.
Axiom id_code : prog id_addr =
 Some (prim (fun stk => match stk with
        | _ :: v :: r :: rest => r :: v :: rest
        | _ => stk
        end)
    :: call :: nil).


Inductive id_spec (N P : RRel) : RRel :=
  | id_call : forall v t,
               represents v t N P ->
              forall r code stk (Q : cfg -> Prop),
                (forall cfg',
                    match cfg' with
                   | Cfg (call :: _) (r' :: v' :: stk') =>
                        r' = r /\ stk' = stk /\
                       represents v' t P N
                   | _ => False
                   end -> Q cfg') ->
               id_spec N P (Cfg (call :: code) (cons (atom id_addr) (atom 0) :: v :: r :: stk)) Q.

Lemma id_spec_anti :
  forall A B, weakenable A -> weakenable B -> subrel A B ->
  forall X, weakenable X -> subrel (id_spec B X) (id_spec A X).
intros.  destruct 1.
pose proof (represents_happy t).
apply id_call with t.
revert H3. apply H5;assumption.
intros.
apply H4.
destruct cfg'.
destruct l;[destruct H6|].
destruct i;[|destruct H6].
destruct l0;[destruct H6|].
destruct l0;[destruct H6|].
intuition.
revert H9. apply H5; assumption.
Qed.

Lemma id_spec_mono :
  forall X Y, weakenable X -> weakenable Y -> subrel X Y ->
  forall A, weakenable A -> subrel (id_spec A X) (id_spec A Y).
intros. destruct 1.
apply id_call with t.
revert H3; apply represents_happy;assumption.
intros. apply H4.
destruct cfg'.
destruct l;[exfalso;assumption|].
destruct i;[|exfalso;assumption].
destruct l0;[exfalso;assumption|].
destruct l0;[exfalso;assumption|].
intuition.
revert H8. apply represents_happy;assumption.
Qed.


Definition mixed_weak (F : RRel -> RRel -> RRel) : Prop :=
  forall (S T : RRel),
    (forall (P Q : cfg -> Prop),
       (forall x, P x -> Q x) ->
       (forall x, T x P -> S x Q)) ->
  forall (X Y : RRel),
    (forall (P Q : cfg -> Prop),
       (forall x, P x -> Q x) ->
       (forall x, X x P -> Y x Q)) ->
    forall (P Q : cfg -> Prop),
       (forall x, P x -> Q x) ->
       forall x, F S X x P -> F T Y x Q.

(*
Inductive derived (F : RRel -> RRel)
                   (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dleaf : X x P -> derived F X x P
  | ddone : P x -> derived F X x P
  | dstep : forall y, step x y -> derived F X y P -> derived F X x P
  | drule' : forall Q, subrel Q (derived F X) -> F Q x P -> derived F X x P.
Definition drule : forall F R x P, F (derived F R) x P -> derived F R x P :=
  fun _ _ _ _ H => drule' _ _ (fun _ _ H => H) H.

Inductive stepF (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | DoneF : P x -> stepF X x P
  | StepF : forall y, step x y -> X y P -> stepF X x P.
*)

Definition hoproof Rules Spec : Prop :=
     forall (Neg Pos : RRel)
       (Neg_ev : subrel (derived Rules (Spec Neg Pos)) Neg)
       (Pos_ev : subrel Pos (derived Rules (Spec Neg Pos))),
       subrel (Spec Neg Pos) (stepF (derived Rules (Spec Neg Pos))).

(*
Inductive trans_rule (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dtrans : forall (Q : cfg -> Prop), X x Q ->
             (forall y, Q y -> X y P) -> trans_rule X x P.
*)

Lemma stepF_weak : forall R, weakenable R -> weakenable (stepF R).
unfold weakenable. intros. destruct H1; eauto using stepF.
Qed.

Lemma trans_weak : forall R, weakenable R -> weakenable (trans_rule R).
unfold weakenable. intros. destruct H1; eauto using trans_rule.
Qed.

Lemma derived_weak1 : forall F R,
  mono F ->
  weakenable R -> weakenable (derived (fun X => weakenize (F X)) R).
intros F R F_mono R_weak.
unfold weakenable.
induction 2;try solve[eauto using derived].
assert (weakenize (F Q0) x Q) by
  (destruct H2 as [P0 []]; exists P0; eauto).
clear H2.
apply drule.
destruct H3 as [P0 []];exists P0.
split;[|tauto].
apply F_mono in H0.
apply H0.
assumption.
Qed.

Lemma derived_trans_weak : forall R,
  weakenable R ->
  weakenable (derived trans_rule R).
intros.
induction 2;try solve[eauto using derived].
destruct H3.
apply drule.
apply dtrans with Q1.
apply H1. assumption.
intros.
eapply H2.
apply H4. assumption.
assumption.
Qed.

Definition union_rrel (R1 R2 : RRel) : RRel :=
  fun x P => R1 x P \/ R2 x P.

Inductive lfp (F : RRel -> RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  Lfp' : forall Q, subrel Q (lfp F) -> F Q x P -> lfp F x P.
Definition Lfp : forall F, subrel (F (lfp F)) (lfp F) :=
  fun F x P H => Lfp' x P (fun _ _ H => H) H.

CoInductive reaches (x : cfg) (P : cfg -> Prop) : Prop :=
  | Done : P x -> reaches x P
  | Step : forall y, step x y -> reaches y P -> reaches x P
  .

Lemma id_weakenable :
 forall X Y : RRel, weakenable X -> weakenable Y ->
   weakenable (id_spec X Y).
intros; unfold weakenable; intros.
destruct H2.
eapply id_call; eauto.
Qed.

(*
Definition adj_weak (F : RRel -> RRel) : Prop :=
  forall (X Y : RRel),
    (forall (P Q : cfg -> Prop),
       (forall x, P x -> Q x) ->
       (forall x, X x P -> Y x Q)) ->
    forall (P Q : cfg -> Prop),
       (forall x, P x -> Q x) ->
       forall x, F X x P -> F Y x Q.
 *)

Lemma id_adj : mixed_weak id_spec.
unfold mixed_weak;intros.
fold (subweak T S) in H.
fold (subweak X Y) in H0.

destruct H2.
apply id_call with t.
revert H2.
apply represents_mixed;assumption.

intros;apply H1;apply H3.
destruct cfg'.
destruct l;[tauto|].
destruct i;[|tauto].
destruct l0;[tauto|].
destruct l0;[tauto|].
intuition.

revert H7;apply represents_mixed;assumption.
Qed.

Lemma id_good :
   forall Neg Pos : RRel,
   weakenable Neg -> weakenable Pos ->
   subrel (derived trans_rule (id_spec Neg Pos)) Neg ->
   subrel Pos (derived trans_rule (id_spec Neg Pos)) ->
   subrel (id_spec Neg Pos) (stepF (derived trans_rule (id_spec Neg Pos))).
intros Neg Pos W_Neg W_Pos H_Neg H_Pos.
unfold subrel;intros.
destruct H.
eapply StepF. constructor. exact id_code.
eapply dstep. constructor. simpl.
eapply ddone.

apply H0.
intuition.
assert (subweak Pos Neg) by firstorder.
revert H. apply represents_mixed;assumption.
Qed.

(* Now need to make sure the soundness can carry through if
   we restrict to only "weakenable" instantiations *)

Require Import Morphisms.
Lemma trans_adj_weak : adj_weak trans_rule.
unfold adj_weak, weak_subrel, subpred, Proper, respectful. firstorder.
Qed.

Lemma trans_sound : forall Claims, derived_stable trans_rule Claims -> sound Claims.
intros. apply deri_sound with trans_rule.
  apply validity_from_m. apply trans_mono. apply trans_valid.
  assumption.
Qed.

Definition id_sound_prop' := @higher_order_stability'
  id_spec id_adj
  trans_rule trans_adj_weak trans_valid trans_sound
  id_good.

Lemma id_sound_prop :
 let derived_lfp :=
       fun Neg : RRel =>
       F.lfp (fun A : RRel => derived trans_rule (id_spec Neg A)):RRel in
 let N := F.union_rrel C.reaches (derived_lfp C.reaches) in
 subrel (id_spec N (derived_lfp N)) C.reaches.
Admitted.

(* Seems like the arguments are swapped between the spec and the represents predicate *)
Lemma id_type : forall N P B (H_pf : subrel (id_spec N P) B),
  subweak N B -> forall A, subweak A P -> forall t,
  represents (cons (atom id_addr) (atom 0)) (func t t) A B.
intros.
simpl.
intros.
apply H_pf. apply id_call with t.
eapply represents_mixed;[| |eassumption];assumption.

intros.
destruct cfg'.
repeat match goal with
|[|- match ?c with _ => _ end] => destruct c;try solve[exfalso;assumption];[idtac]
end.
intuition.
eapply represents_mixed;[| |eassumption];assumption.
Qed.
