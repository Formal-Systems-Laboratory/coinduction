Require Import himp_syntax.

(* Some lemmas asserting that the generated injection/projection functions
   properly implement subsorting *)

Definition NormK t :=
  match t with
  | KExp e => ExpToK e
  | _ => t
  end.
Definition IsNormK t := t = NormK t.

Lemma ExpNormK : forall t, IsNormK (ExpToK t).
  destruct t; reflexivity.
Qed.
Lemma ExpInK : forall t, ExpFromK (ExpToK t) = Some t.
  destruct t;reflexivity.
Qed.
Lemma ExpOfK : forall t, IsNormK t ->
  match ExpFromK t with
  | Some e => ExpToK e = t
  | None => True
  end.
destruct t; try reflexivity.
intro H. 
rewrite H.
simpl.
rewrite ExpInK.
reflexivity.
Qed.

Lemma KResultNormK : forall t, IsNormK (KResultToK t).
  destruct t;reflexivity.
Qed.
Lemma KResultInK : forall t, KResultFromK (KResultToK t) = Some t.
  destruct t;reflexivity.
Qed.
Lemma KResultOfK : forall t, IsNormK t ->
  match KResultFromK t with
  | Some e => KResultToK e = t
  | None => True
  end.
destruct t; try reflexivity.
Qed.

Definition KResultInExp : forall t, KResultFromExp (KResultToExp t) = Some t.
  destruct t;reflexivity.
Qed.
Definition KResultOfExp : forall t,
  match KResultFromExp t with
  | Some e => KResultToExp e = t
  | None => True
  end.
destruct t;try reflexivity.
Qed.

Lemma coherence_KResult_Exp_K : forall t, KResultToK t = ExpToK (KResultToExp t).
  destruct t;reflexivity.
Qed.

Definition coherent {C A B : Type} (f_ac : A -> C) (f_ab : A -> B) (f_bc : B -> C) : Prop :=
  forall a, f_ac a = f_bc (f_ab a).

Lemma coherent_link : forall {T X Y Z : Type} (up1 : X -> T) (up2 : Y -> T) (up3 : Z -> T) along1 along2,
  coherent up1 along1 up2 -> coherent up2 along2 up3 -> coherent up1 (fun x => along2 (along1 x)) up3.
congruence.
Qed.

(* So we just need coherence for K and the one-step thingies? *)
