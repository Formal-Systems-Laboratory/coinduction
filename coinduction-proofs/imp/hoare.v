Require Import String.
Require Import ZArith.

Set Implicit Arguments.

Open Scope string.
Open Scope Z.

Require Import imp.

(* Defining a pure subset of expressions,
   extented to allow functions from the logic *)
Inductive exp :=
  | var : string -> exp
  | con : Z -> exp
  | plus : exp -> exp -> exp
  | app : (Z -> Z) -> exp -> exp
  .
Inductive bexp :=
  | bcon : bool -> bexp
  | le : exp -> exp -> bexp
  | eql : exp -> exp -> bexp
  | not : bexp -> bexp
  | and : bexp -> bexp -> bexp
  .
Fixpoint eval_e env e :=
  match e with
    | var v => env v
    | con z => z
    | plus e1 e2 => eval_e env e1 + eval_e env e2
    | app f e => f (eval_e env e)
  end.
Fixpoint eval_b env e :=
  match e with
    | bcon b => b
    | le e1 e2 => Z.leb (eval_e env e1) (eval_e env e2)
    | eql e1 e2 => Z.eqb (eval_e env e1) (eval_e env e2)
    | not b => negb (eval_b env b)
    | and b1 b2 => if eval_b env b1 then eval_b env b2 else false
  end.

(* pure boolean expressions are currently re-used as formulas.
   Supporting quantifiers probably requires distinguishing the types *)
Definition formula := bexp.
Definition holds f env := eval_b env f = true.

(* Identification and extraction of pure from general
   expressions is done with partial functions *)
Definition lift {A B} (f : A -> B) (oa : option A) : option B :=
  match oa with
    | Some a => Some (f a)
    | None => None
  end.
Arguments lift _ _ f !oa.
Definition lift2 {A B C} (f : A -> B -> C) (oa : option A) (ob : option B) : option C :=
  match oa with
    | Some a => lift (f a) ob
    | _ => None
  end.
Fixpoint is_pure_e (e : imp.exp) : option exp :=
  match e with
    | imp.var x => Some (var x)
    | imp.con z => Some (con z)
    | imp.plus e1 e2 => lift2 plus (is_pure_e e1) (is_pure_e e2)
    | _ => None
  end.
Fixpoint is_pure_b (b : imp.bexp) : option bexp :=
  match b with
    | imp.bcon b => Some (bcon b)
    | imp.le e1 e2 => lift2 le (is_pure_e e1) (is_pure_e e2)
    | imp.eql e1 e2 => lift2 eql (is_pure_e e1) (is_pure_e e2)
    | imp.not e => lift not (is_pure_b e)
    | imp.and e1 e2 => lift2 and (is_pure_b e1) (is_pure_b e2)
  end.

(* Defining the semantic notion of satisfaction of a triple,
   and the proof system *)
Definition valid (P : formula) (s : stmt) (Q : formula) : Prop :=
  forall env, holds P env -> forall n env', trc step_s n (s,env) (skip,env') -> holds Q env'.

Definition impl P Q := forall env, holds P env -> holds Q env.

Fixpoint subst_e x r e :=
  match e with
    | var x' => if string_dec x x' then r else e
    | con _ => e
    | plus e1 e2 => plus (subst_e x r e1) (subst_e x r e2)
    | app f e => app f (subst_e x r e)
  end.
Fixpoint subst x r b :=
  match b with
    | bcon _ => b
    | le e1 e2 => le (subst_e x r e1) (subst_e x r e2)
    | eql e1 e2 => eql (subst_e x r e1) (subst_e x r e2)
    | not b1 => not (subst x r b1)
    | and b1 b2 => and (subst x r b1) (subst x r b2)
  end.

Inductive proof : formula -> stmt -> formula -> Set :=
  | p_conseq_l : forall P P' Q s, proof P' s Q -> impl P P' -> proof P s Q
  | p_conseq_r : forall P Q Q' s, proof P s Q' -> impl Q' Q -> proof P s Q
  | p_assign : forall Q x e0 e, is_pure_e e0 = Some e -> proof (subst x e Q) (assign x e0) Q
  | p_skip : forall Q, proof Q skip Q
  | p_seq : forall P Q R s1 s2, proof P s1 Q -> proof Q s2 R -> proof P (seq s1 s2) R
  | p_cond : forall P b0 b s1 s2 Q, is_pure_b b0 = Some b ->
          proof (and P b) s1 Q -> proof (and P (not b)) s2 Q ->
                 proof P (cond b0 s1 s2) Q
  | p_while : forall P b0 b s, is_pure_b b0 = Some b -> 
     proof (and P b) s P -> proof P (while b0 s) (and P (not b))
  .

(* Proving soundness requires various lemmas.
   Relating small-step execution of pure expresions to
   the evaluation functions takes much of the effort.
 *)

(* relating "set" and substitution *)
Lemma eval_e_subst : forall x r e env, eval_e env (subst_e x r e) = eval_e (set env x (eval_e env r)) e.
Proof. induction e;simpl;[unfold set;destruct (string_dec x s);simpl|..];congruence. Qed.

Lemma eval_subst : forall x r env e, eval_b env (subst x r e) = eval_b (set env x (eval_e env r)) e.
Proof.
induction e;simpl;rewrite ?eval_e_subst;try congruence.
rewrite IHe1, IHe2; reflexivity.
Qed.

Definition pure_pres {E Epure : Set} (is_pure : E -> option Epure)
                     {Res : Set} (eval : Env -> Epure -> Res) e e1 :=
  match is_pure (fst e) with
    | Some e' => snd e1 = snd e /\
        match is_pure (fst e1) with
          | Some e1' => eval (snd e) e1' = eval (snd e) e'
          | None => False
        end
    | None => True
  end.

Lemma pure_pres_refl : forall {E Ep} is {R} eval a, @pure_pres E Ep is R eval a a.
Proof. intros;unfold pure_pres. destruct (is (fst a));split;reflexivity. Qed.
Lemma pure_pres_trans : forall {E Ep} is {R} eval a b c,
   @pure_pres E Ep is R eval a b -> pure_pres is eval b c -> pure_pres is eval a c.
Proof. unfold pure_pres;intros.
  destruct (is (fst a));[destruct H|trivial]. 
  destruct (is (fst b));[destruct H0|destruct H1].
  split;[|destruct (is (fst c))];congruence.
Qed.

Lemma pure_pres_trc : forall {E Ep} is {R} eval n a b,
  trc (@pure_pres E Ep is R eval) n a b -> pure_pres is eval a b.
Proof. induction 1;subst;eauto using pure_pres_trans,pure_pres_refl. Qed.

Ltac pure_pres_tac := repeat match goal with
| [H : match is_pure_e ?x with _ => _ end |- _] => destruct (is_pure_e x);simpl;[|destruct H;exact I]
| [H : match is_pure_b ?x with _ => _ end |- _] => destruct (is_pure_b x);simpl;[|destruct H;exact I]
| [H : True |- _] => clear H
| [H : False |- _] => destruct H
| [H : _ /\ _ |- _] => destruct H
end;try (split;congruence).

Lemma eval_e_step : forall a b, step_e a b -> pure_pres is_pure_e eval_e a b.
Proof.
induction 1;unfold pure_pres in * |- *;simpl in * |- *;pure_pres_tac.
destruct (is_pure_e b);simpl;split;congruence.
Qed.

Lemma eval_e_result : forall e v n env env', trc step_e n (e, env) (imp.con v, env') ->
  forall e', is_pure_e e = Some e' -> env' = env /\ v = eval_e env e'.
Proof.
intros. apply (map_trc eval_e_step) in H. apply pure_pres_trc in H.
unfold pure_pres in H;simpl in H;rewrite H0 in H. assumption.
Qed.

Lemma eval_b_step : forall a b, step_b a b -> pure_pres is_pure_b eval_b a b.
Proof.
induction 1;repeat match goal with [H : step_e _ _ |- _] => apply eval_e_step in H end;
unfold pure_pres in * |- *;simpl in * |- *;pure_pres_tac;
match goal with [|- match lift _ ?x with _ => _ end] =>
  destruct x eqn:?;simpl;pure_pres_tac
end.
destruct b;[rewrite Heqo|];split;reflexivity.
rewrite H1;split;congruence.
Qed.

Lemma eval_b_result : forall e v n env env', trc step_b n (e, env) (imp.bcon v, env') ->
  forall e', is_pure_b e = Some e' -> env' = env /\ v = eval_b env e'.
Proof.
intros. apply (map_trc eval_b_step) in H. apply pure_pres_trc in H.
unfold pure_pres in H;simpl in H;rewrite H0 in H. assumption.
Qed.

(* tactics for working with option *)
Ltac option_lift_cleanup := repeat match goal with
| [H : lift ?f ?e = Some ?v |- _] => is_var v;
  destruct e eqn:?;[|discriminate H];injection H;clear H;intro;subst v
| [H : Some ?e = Some ?v |- _] => is_var v;
  injection H;clear H;intro;subst v
| [H : None = Some _ |- _] => discriminate H
| [H : lift2 ?f ?e1 ?e2 = Some ?v |- _] => is_var v;
  destruct e1 eqn:?;[simpl in H|discriminate H]
| [H : forall x, Some _ = Some x -> _ |- _] => specialize (H _ (eq_refl _))
| [H : forall x, ?e = Some x -> _, H2 : ?e = Some _ |- _] => specialize (H _ H2)
| [H : _ /\ _ |- _] => destruct H
| [H : exists _, _ |- _] => destruct H
end.

(* Tactics for induction over trc of step -
   The built-in induction tactics do not usually give useful induction hypotheses
   if indices of a dependent type have structure, like "step_e (a,b) (c,d)".
   This case should work because every pair has that form, and we help it along by
   abstracting a given pair to a single variable.
 *)
Ltac prep_trc :=
  match goal with [H : trc _ _ ?P ?Q |- _] =>
  remember P as p eqn:Heqp; remember Q as q eqn:Heqq; move Heqq at top; move Heqp at top; move H at top
  end.
Ltac trc_ind := intros;prep_trc;let rec reverts := match goal with [H : _ |- _] =>
  match type of H with trc _ _ _ _ => induction H | _ => revert H;reverts end end
in reverts.

Lemma assign_dec : forall x e n env env', trc step_s n (assign x e, env) (skip, env') ->
  exists v k env'', trc step_e k (e, env) (imp.con v, env'') /\ (k < n)%nat /\ set env'' x v = env'.
Proof.
trc_ind;intros;subst;[congruence| ].
inversion H;subst. (* splitting on how assign x e took a step *)
  (* at last step *)
  clear IHtrc. inversion H0;subst;[ | inversion H1]. injection H1.
  repeat eexists;eauto using done.
  (* stepping in e. *)
  specialize (IHtrc _ _ _ (eq_refl _) _ (eq_refl _)).
  destruct IHtrc as (v & k & env''& [? []]). exists v, (S k), env''.
  intuition. eapply step;eassumption.
Qed.

Lemma seq_dec : forall s1 s2 n env env', trc step_s n (seq s1 s2, env) (skip, env') ->
  exists env'' k1 k2, trc step_s k1 (s1, env) (skip, env'') /\ trc step_s k2 (s2, env'') (skip, env')
    /\ (k1 + k2 < n)%nat.
Proof.
trc_ind;intros;subst.
congruence.
inversion H;subst.
  (* was finished *)
  clear IHtrc;repeat eexists;eauto using done with arith.
  (* evaluating statement 1 *)
  specialize (IHtrc _ _ _ (eq_refl _) _ (eq_refl _)).
  decompose record IHtrc;clear IHtrc.
  repeat eexists;eauto using step with arith.
Qed.

Lemma cond_dec : forall c s1 s2 n env env', trc step_s n (cond c s1 s2, env) (skip, env') ->
  exists b env'' k1 k2, trc step_b k1 (c, env) (imp.bcon b, env'') /\
       trc step_s k2 (if b then s1 else s2, env'') (skip, env') /\
       (k1 + k2 < n)%nat.
Proof.
trc_ind;intros;subst;[congruence| ].
inversion H; clear H; subst.
  (* was finished *)
  repeat eexists;eauto using done with arith.
  (* evaluating in condition *)
  specialize (IHtrc _ _ _ _ (eq_refl _) _ (eq_refl _)).
  decompose record IHtrc;clear IHtrc.
  repeat eexists;eauto using step with arith.
Qed.

Inductive while_trace b s env : Env -> Prop :=
 | while_done : eval_b env b = false -> forall env', env' = env -> while_trace b s env env'
 | while_step : eval_b env b = true ->
     forall n env', trc step_s n (s, env) (skip, env') ->
     forall env'', while_trace b s env' env'' ->
        while_trace b s env env''
 .

Lemma while_dec : forall n b s env env', trc step_s n (while b s, env) (skip, env') ->
  forall b', is_pure_b b = Some b' -> while_trace b' s env env'.
Proof.
intro n. pattern n. apply (well_founded_induction lt_wf). clear n.
intros.
match goal with [H : trc _ _ _ _  |- _] => inversion H;clear H;subst end. congruence.
match goal with [H : step_s _ _  |- _] => inversion H;clear H;subst end.
match goal with [H : _ |- _] => apply cond_dec in H;decompose record H;clear H end.
match goal with [H : _ |- _] => eapply eval_b_result in H;[|eassumption];destruct H;subst end.
destruct (eval_b env b') eqn:?.
(* loop condition evaluated to true, take a step *)
apply seq_dec in H2;decompose record H2;clear H2.
  eapply while_step, H;try eassumption. omega.
(* false, finish now *)
apply while_done. assumption.
inversion H2;[|solve[inversion H0]];congruence.
Qed.

Lemma sound : forall P s Q, proof P s Q -> valid P s Q.
induction 1;unfold valid in * |- *;simpl;intros.
(* conseq l *)
eauto.
(* conseq r *) 
eauto.
(* assign *)
apply assign_dec in H0;decompose record H0;clear H0.
eapply eval_e_result in H2;[|eassumption]. destruct H2. subst.
unfold holds. rewrite <- eval_subst. assumption.
(* skip *)
inversion H0;subst. congruence. inversion H1.
(* seq *)
specialize (IHproof1 _ H1); clear H1.
apply seq_dec in H2. decompose record H2;clear H2.
  specialize (IHproof1 _ _ H3). specialize (IHproof2 _ IHproof1 _ _ H1). assumption.
(* cond *)
apply cond_dec in H2;decompose record H2;clear H2.
eapply eval_b_result in H3;[|eassumption];destruct H3;subst.
revert H4. destruct (eval_b env b) eqn:?;[apply IHproof1|apply IHproof2];
unfold holds;simpl;rewrite H1, Heqb1;reflexivity.
(* while *)
eapply while_dec in H1;[|eassumption]. induction H1.
subst env'. unfold holds. simpl. rewrite H1, H0. reflexivity.
apply IHproof in H2. auto. unfold holds. simpl. rewrite H0. assumption.
Qed.

Require Import example.

Definition zero_loop_pf : proof (le (con 0) (var "x"))
                                zero_loop
           (and (le (con 0) (var "x")) (le (var "x") (con 0))).
eapply p_conseq_r.
eapply p_while. reflexivity.
eapply p_conseq_l.
eapply p_assign. reflexivity.
Ltac pre_impl := let env := fresh "env" in intro env; unfold holds; simpl;
  repeat match goal with [|- context[env ?v]] => generalize (env v);intro end;clear env.
pre_impl. destruct (Z.leb_spec 0 z);[|discriminate]. rewrite ?Z.leb_le. auto with zarith.
pre_impl. destruct (Z.leb_spec 0 z);[|discriminate]. rewrite Bool.negb_true_iff, ?Z.leb_le, ?Z.leb_gt.
  auto with zarith.
Defined.

Lemma zero_loop : valid (le (con 0) (var "x")) (while (imp.le (imp.con 1) (imp.var "x"))
                                          (assign "x" (imp.plus (imp.var "x") (imp.con (-1)))))
           (and (le (con 0) (var "x")) (le (var "x") (con 0))).
Proof. exact (sound zero_loop_pf). Qed.

Section sum_code.
Import imp.
Local Coercion con : Z >-> exp.
Local Coercion var : string >-> exp.

Definition sum_loop' : stmt :=
  seq (while (not (eql "n" 0)) (seq (assign "n" (plus "n" (-1)))
                                    (assign "s" (plus "s" "n"))))
      (assign "n" (plus "n" (-1))).
End sum_code.

Lemma bool_if : forall (a b c d : bool),
  ((if a then b else c) = d) <-> (a = true /\ b = d) \/ (a = false /\ c = d).
Proof. destruct a;intuition congruence. Qed.

Lemma diff_false_true_iff : false = true <-> False.
Proof. pose proof Bool.diff_true_false. intuition. Qed.
Lemma and_false : forall P, (P /\ False) <-> False.
Proof. tauto. Qed.
Lemma or_false : forall P, (P \/ False) <-> P.
Proof. tauto. Qed.

Local Coercion con : Z >-> exp.
Local Coercion var : string >-> exp.

Definition sum_pf : proof (and (le 0 "n") (eql (plus "s" (app sum_to (plus "n" (-1))))
                                               (plus "S" (app sum_to "N"))))
                          sum_loop'
                          (eql (var "s") (plus (var "S") (app sum_to (var "N")))).
Proof.
eapply p_seq;[|eapply p_assign;reflexivity].
eapply p_conseq_r.
eapply p_while;[reflexivity|].
eapply p_seq;[|eapply p_assign;reflexivity];eapply p_conseq_l;[eapply p_assign;reflexivity|].

simpl. pre_impl.
rewrite ?bool_if, ?Bool.negb_true_iff, ?Bool.negb_false_iff, ?diff_false_true_iff,
  ?and_false, ?or_false,
  ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le, ?Z.leb_gt.
  intuition.  rewrite <- H2;clear H2.
rewrite (sum_to_equation (z + -1)).
destruct (Z.ltb_spec (z + -1) 0);[exfalso|];auto with zarith.

simpl. pre_impl.
rewrite ?bool_if, ?Bool.negb_true_iff, ?Bool.negb_false_iff, ?diff_false_true_iff,
  ?and_false, ?or_false,
  ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le, ?Z.leb_gt.
  intuition.  rewrite <- H2;clear H2.
subst. rewrite sum_to_equation. simpl. auto with zarith.
Qed.