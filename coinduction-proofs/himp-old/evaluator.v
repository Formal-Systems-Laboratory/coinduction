Require Import kstyle.
Require Import domains.

Require Import ZArith.
Require Import String.
Require Import List.

Set Implicit Arguments.

Section MapSplit.
  Variable K : Type.
  Variable k_dec : forall (x y : K), {x=y}+{x<>y}.

  Fixpoint map_split k {V} m : option (V * Map K V) :=
  match m with
    | mapEmpty => None
    | (k' |-> v) => if k_dec k k' then Some (v, mapEmpty) else None
    | (l :* r) =>
      match map_split k l with
        | Some (v, mapEmpty) => Some (v, r)
        | Some (v, l') => Some (v, l' :* r)
        | None =>
          match map_split k r with
            | Some (v, r') => Some (v, l :* r')
            | None => None
          end
      end
  end.
  Functional Scheme map_split_ind := Induction for map_split Sort Prop.

  Lemma map_split_sound k {V} (m : Map K V) :
    match map_split k m with
      | Some (v, m') => m ~= k |-> v :* m'
      | None => True
    end.
  Proof.
  functional induction (map_split k m);auto;try equate_maps;
  match goal with [H : map_split ?x ?m = _, IH : match map_split ?x ?m with None => _ | _ => _ end
                   |- _] => rewrite H in IH; rewrite IH end;equate_maps.
  Qed.

  Lemma map_split_sound' k {V} (v : V) m m' :
    map_split k m = Some (v, m') -> m ~= k |-> v :* m'.
  Proof.
    pose proof (map_split_sound k m).
    intro.
    rewrite H0 in H.
    assumption.
  Qed.

  Inductive HasKey (x : K) {V} : Map K V -> Prop :=
  | key_here : forall v, HasKey x (x |-> v)
  | key_left : forall env env', HasKey x env -> HasKey x (env :* env')
  | key_right : forall env env', HasKey x env' -> HasKey x (env :* env')
  .

  Lemma transport_has_key x {V} (env env' : Map K V) :
    env ~= env' -> (HasKey x env <-> HasKey x env').
  Proof.
    induction 1; split;intros;
    repeat match goal with [H : HasKey _ ?V |- _] => (is_var V;fail 1) || (inversion H; clear H; subst) end;
    repeat match goal with [H : _ <-> _ |- _] => destruct H end;
    eauto using key_left, key_right, key_here.
  Qed.

  Definition has_key (x : K) {V} (m : Map K V) :=
    exists v env', m ~= x |-> v :* env'.

  Lemma rep x {V} (env : Map K V) :
    has_key x env -> HasKey x env.
  Proof.
    destruct 1 as [v [env' H]].
    apply (transport_has_key x) in H.
    apply H.
    eauto using key_left, key_right, key_here.
  Qed.

  Lemma rep_inv x {V} (env : Map K V) :
    HasKey x env -> has_key x env.
    induction 1.
    eexists. eexists. symmetry. apply equivUnit.
    destruct IHHasKey as [v [env'' IH]].
    exists v. exists (env'' :* env').
    rewrite IH. equate_maps.
    destruct IHHasKey as [v [env'' IH]].
    exists v. exists (env :* env'').
    rewrite IH. equate_maps.
  Qed.

  (* Without enforcing definedness there might be duplicate labels, but str_split finds some label *)
  Lemma map_split_completeish : forall x {V} (env : Map K V),
    has_key x env -> if map_split x env then True else False.
  Proof.
    induction env; intros; apply rep in H; inversion H; subst; simpl;
    repeat match goal with
        | [|- if if k_dec ?x ?y then _ else _ then _ else _] => destruct (k_dec x y);auto
        | [|- if match map_split ?x ?env with  _ => _ end then _ else _] =>
          destruct (map_split x env) as [[? []]|];auto using rep_inv
    end.
  Qed.
End MapSplit.

Definition str_split := map_split string_dec.
Definition str_split_sound k V (m : Map string V) :
       match str_split k m with
       | Some (v, m') => m ~= k |-> v :* m'
       | None => True
       end
 := map_split_sound string_dec k m.
Definition str_split_sound' : 
 forall k V v (m m' : Map string V),
       str_split k m = Some (v, m') -> m ~= k |-> v :* m'
 := map_split_sound' string_dec.
Definition str_split_completeish
 : forall x V (env : Map string V),
       has_key x env -> if str_split x env then True else False
 := map_split_completeish string_dec.

Definition eval cfg : option kcfg :=
  match cfg with
    | KCfg nil env heap lenv => None
    | KCfg (item1 :: rest) env heap lenv =>
      let exp_step e' := Some (KCfg e' env heap lenv) in
      let heat_step e' f := exp_step (kra e' (kra f rest)) in
      let exp1_step e' := exp_step (e' :: rest) in
      match item1 with
        | EAmb l _ => exp1_step l
        | ECon i =>
          match rest with
            | (KFreezeE f :: rest') => exp_step (f (ECon i) :: rest')
            | _ => None
          end
        | BCon b =>
          match rest with
            | (KFreezeB f :: rest') => exp_step (f (BCon b) :: rest')
            | _ => None
          end
        | EVar x => 
          match str_split x env with
            | None => None
            | Some (v,env') => Some (KCfg (kra (ECon v) rest) (x |-> v :* env') heap lenv)
          end
        | ELoad (ECon i) =>
          match map_split Z.eq_dec i heap with
            | None => None
            | Some (j, _) => Some (KCfg (kra (ECon j) rest) env heap lenv)
          end
        | ELoad e => heat_step e (KFreezeE ELoad)
        | SAssign x (ECon i) =>
          match str_split x env with
            | None => None
            | Some (_, env') => Some (KCfg rest (x |-> i :* env') heap lenv)
          end
        | SAssign x e => heat_step e (x :=□)
        | HAssign (ECon i) (ECon j) =>
          match map_split Z.eq_dec i heap with
            | None => None
            | Some (_, heap') => Some (KCfg rest env (i |-> j :* heap') lenv)
          end
        | HAssign (ECon i) e => heat_step e (FreezeR HAssign (ECon i))
        | HAssign e e2 => heat_step e (FreezeL HAssign e2)
        | Jump (ECon l) =>
          match map_split Z.eq_dec l lenv with
            | None => None
            | Some (s, _) => Some (KCfg (kra s kdot) env heap lenv)
          end
        | Jump e => heat_step e (KFreezeE Jump)
        | EPlus (ECon i) (ECon j) => exp1_step (ECon (Zplus i j))
        | EPlus (ECon i) e2       => heat_step e2 (ECon i + □)
        | EPlus e1 e2             => heat_step e1 (□ + e2)
        | EMinus (ECon i) (ECon j) => exp1_step (ECon (Zminus i j))
        | EMinus (ECon i) e2       => heat_step e2 (ECon i - □)
        | EMinus e1 e2             => heat_step e1 (□ - e2)
        | EDiv (ECon i) (ECon j) =>
          if Zneq_bool 0%Z j then exp1_step (ECon (Zdiv i j)) else None
        | EDiv (ECon i) e2       => heat_step e2 (ECon i /□)
        | EDiv e1 e2             => heat_step e1 (□/ e2)
        | BNot (BCon b)          => exp1_step (BCon (negb b))
        | BNot b                => heat_step b (KFreezeB BNot)
        | BLe (ECon i) (ECon j) => exp1_step (BCon (Zle_bool i j))
        | BLe (ECon i) e2       => heat_step e2 (i <=□)
        | BLe e1 e2             => heat_step e1 (□<= e2)
        | BEq (ECon i) (ECon j) => exp1_step (BCon (i =? j)%Z)
        | BEq (ECon i) e2       => heat_step e2 (i ==□)
        | BEq e1 e2             => heat_step e1 (□== e2)
        | BAnd (BCon b) be2 => if b then exp1_step be2 else exp1_step (BCon false)
        | BAnd be1 be2 => heat_step be1 (□&& be2)
        | Skip => exp_step rest
        | SIf (BCon b) s1 s2 => if b then exp1_step s1 else exp1_step s2
        | SIf be s1 s2 => heat_step be (if□then s1 else s2)
        | SWhile b s => exp1_step (SIf b (Seq s (SWhile b s)) Skip)
        | Seq s1 s2 => heat_step s1 s2

        | KFreezeE _ => None
        | KFreezeB _ => None
      end
end.

Functional Scheme eval_ind := Induction for eval Sort Prop.

Lemma eval_sound : forall cfg, match eval cfg with Some cfg' => kstep cfg cfg' | None => True end.
Proof.
intros;functional induction (eval cfg);unfold str_split in * |-;
repeat match goal with
  [H : map_split _ _ _ = _ |- _] => apply map_split_sound' in H end;
econstructor(reflexivity || eassumption).
Qed.

Lemma eval_completeish : forall cfg cfg', kstep cfg cfg' ->
                                          match eval cfg with
                                                         Some cfg'' => kstep cfg cfg''
                                                       | None => False end.
Proof.
Ltac good_split H dec x env :=
  let H0 := fresh in
  assert (has_key x env) as H0 by (clear -H;firstorder);
  apply (map_split_completeish dec) in H0;
  pose proof (map_split_sound dec x env);
  destruct (map_split dec x env) as [[]|];[clear H0|solve[destruct H0]].

intros;destruct H eqn:?;simpl;unfold str_split in *|-*;try solve[repeat match goal with
  | [H : ?env ~= ?x |-> _ :* _ |- context [match map_split ?dec ?x ?env with None => _ | _ => _ end]] =>
    good_split H dec x env
  | [|- kstep _ _] => econstructor (eassumption || reflexivity)
  | [H : Zneq_bool ?x ?y = _ |- context [if Zneq_bool ?x ?y then _ else _]] => rewrite H
  | [|- context [match ?e with EVar _ => _ | _ => _ end]] => destruct e; try discriminate
  | [|- context [match ?b with BCon _ => _ | _ => _ end]] => destruct b; try discriminate
end].
Qed.