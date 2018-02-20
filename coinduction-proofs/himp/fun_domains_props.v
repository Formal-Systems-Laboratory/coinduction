Require Export himp_cfg_and_prims.
Require Import equate_map_reflection.
Require Import patterns.

Require Import himp_claims.

Require Import Setoid.
Require Import ZArith.

Fixpoint stk_equiv (s1 s2 : list Frame) : Prop :=
  match s1, s2 with
    | nil, nil => True
    | frame k1 e1::s1', frame k2 e2::s2' =>
      k1 = k2 /\ e1 ~= e2 /\ stk_equiv s1' s2'
    | _, _ => False
  end.

Definition kequiv (k1 k2 : kcfg) : Prop :=
  match k1, k2 with
    | KCfg k1 store1 stk1 heap1 funs1 mark1,
      KCfg k2 store2 stk2 heap2 funs2 mark2 =>
      k1 = k2 /\ store1 ~= store2 /\ stk_equiv stk1 stk2
      /\ heap1 ~= heap2 /\ funs1 ~= funs2 /\ mark1 = mark2
  end.

Add Morphism KCfg with signature
  @eq k ==> MapEquiv ==> stk_equiv ==> MapEquiv ==> MapEquiv ==> @eq Z ==> kequiv as KCfg_mor.
Proof. firstorder. Qed.

(** A predicate saying two stacks are equivalent,
    requires exact equality of the code but compares
    environments up to map equality *)

Definition returning' c e c' : Prop :=
     match c' with
       | KCfg (kra (KStmt (SReturn e')) _) _ stack' heap' functions' _ =>
         match c with
           | KCfg kcell _ stack heap functions alloc_mark =>
               e = e'
               /\ stk_equiv stack stack'
               /\ heap ~= heap'
               /\ functions ~= functions'
         end
       | _ => False
     end.

Lemma returning_returns : forall c e c', returning' c e c' ->
  exists krest,
  kcell c' = kra (KStmt (SReturn e)) krest.
Proof.
destruct c'.
simpl;intro H.
repeat match type of H with
| (match ?x with _ => _ end) => destruct x;try solve[destruct H];[idtac]
end.
intuition.
exists kcell.
congruence.
Qed.

Definition returning c v := returning' c (ECon v).
Inductive returns (c : kcfg) (v : Z) : kcfg -> (kcfg -> Prop) -> Prop :=
  returns_claim : returns c v c (returning c v).

Definition returning_bool c b := returning' c (BCon b).
Inductive returns_bool (c : kcfg) (v : bool) : kcfg -> (kcfg -> Prop) -> Prop :=
  returns_bool_claim : returns_bool c v c (returning_bool c v).

Definition get_returning (c : kcfg) : option Z :=
  match kcell c with
    | kra (KStmt (SReturn (ECon v'))) _ => Some v'
    | _ => None
  end.
Lemma get_returning_returns : forall c,
  match get_returning c with
    | Some v => exists krest, kcell c = kra (KStmt (SReturn (ECon v))) krest
    | None => True
  end.
Proof.
destruct c.
unfold get_returning. simpl.
repeat match goal with
| [|- match (match ?x with _ => _ end) with _ => _ end]
   => destruct x;try (exact I)
end.
eexists.
reflexivity.
Qed.

Lemma use_returning : forall ckcell cstore cstk cheap cfunctions cmark
     e (Q : kcfg -> (kcfg -> Prop) -> Prop) (P : kcfg -> Prop),
  (forall kstore kheap kfunctions kmark,
    cheap ~= kheap ->
    cfunctions ~= kfunctions ->
   forall kstk,
    stk_equiv cstk kstk ->
   forall krest,
    Q (KCfg (kra (KStmt (SReturn e)) krest)
            kstore kstk kheap kfunctions kmark) P
   ) ->
  (forall k', returning'
     (KCfg ckcell cstore cstk cheap cfunctions cmark)
    e k' -> Q k' P).
intros.
pose proof (returning_returns _ _ _ H0).
destruct H1.
destruct k';simpl in * |- *;subst.
intuition.
Qed.

Lemma expose_frame : forall p m stk (Q : list Frame -> Prop),
  (forall m' stk',
     m' ~= m -> stk_equiv stk stk' -> Q (frame p m'::stk')) ->
  (forall stk',
     stk_equiv (frame p m::stk) stk' -> Q stk').
intros.
destruct stk';[solve[destruct H0]|].
destruct f.
simpl in H0.
intuition. subst.
symmetry in H0.
auto.
Qed.

(* Somehow simple "apply" doesn't unify well enough *)
Ltac use_expose_frame := refine (expose_frame _ _ _ _ _).
