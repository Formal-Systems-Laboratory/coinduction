Require Import String.
Require Import ZArith.

(* Hoare logic, directly allowing side-effects in expressions.
  Follows the development in "Hoare Logic for NanoJava"
 *)

Set Implicit Arguments.

Open Scope string.
Open Scope Z.

Require Import imp.

(* We use a shallow embedding of predicates here *)
Definition formula := Env -> Prop.

(* Defining the satisfaction of the triples used to specify statements and expressions *)
(* A triple for a statement gives a formula assumed true in the initial environment,
   and a postcondition that should hold in any final environment *)
Definition valid_s (P : formula) (s : stmt) (Q : formula) : Prop :=
  forall env, P env -> forall n env', trc step_s n (s,env) (skip,env') -> Q env'.
(* The specifications of expressions need access to the result of the expression *)
Definition valid_e (P : formula) (e : imp.exp) (Q : Z -> formula) : Prop :=
  forall env, P env -> forall n r env', trc step_e n (e,env) (imp.con r,env') -> Q r env'.
Definition valid_b (P : formula) (e : imp.bexp) (Q : bool -> formula) : Prop :=
  forall env, P env -> forall n r env', trc step_b n (e,env) (imp.bcon r,env') -> Q r env'.

(* Now we define the judgements for proving these sorts of claims.
   First we introduce some auxiliary definitions which will be used to state the rules. *)
Definition impl (P Q : formula) := forall env, P env -> Q env.

Inductive proof_e : formula -> exp -> (Z -> formula) -> Type :=
  | p_var : forall x Q, proof_e (fun env => Q (env x) env) (var x) Q
  | p_con : forall z Q, proof_e (Q z) (con z) Q
  | p_plus : forall P e1 Q1 e2 Q2,
      proof_e P e1 Q1 -> (forall r, proof_e (Q1 r) e2 (Q2 r)) ->
      forall Q, (forall r1 r2, impl (Q2 r1 r2) (Q (r1+r2))) ->
      proof_e P (plus e1 e2) Q
  | p_postdec : forall x Q,
      proof_e (fun env => Q (env x) (set env x (env x - 1))) (postdec x) Q
  | p_conseq_e : forall {A : Set} P' e Q', (forall (Z:A), proof_e (P' Z) e (Q' Z)) ->
       forall (P : formula) (Q : Z -> formula) , (forall s v t, (forall Z, P' Z s -> Q' Z v t) -> (P s -> Q v t)) ->
       proof_e P e Q
  .

Lemma p_conseq_e_l : forall P' e Q, proof_e P' e Q ->
    forall (P : formula), (forall s, P s -> P' s) -> proof_e P e Q.
Proof. intros; apply (@p_conseq_e unit (fun _ => P') e (fun _ => Q));firstorder. Qed.
Lemma p_conseq_e_r : forall P e Q', proof_e P e Q' ->
    forall (Q : Z -> formula),
      (forall v t, Q' v t -> Q v t) -> proof_e P e Q.
Proof. intros; apply (@p_conseq_e unit (fun _ => P) e (fun _ => Q'));firstorder. Qed.

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

Definition strict {A E : Set} (R_A : (A*E) -> (A*E) -> Prop)
  {B : Set} (R_B : (B*E) -> (B*E) -> Prop) (f : B -> A)
  {C : Set} (con : C -> B) : Prop :=
  forall b1 e1 a2 e2, R_A (f b1,e1) (a2,e2) ->
    ((exists x, b1 = con x) \/ exists b2, a2 = f b2 /\ R_B (b1,e1) (b2,e2)).

Definition strict_decompose :
  forall {A E R_A B R_B} f {C} con (Hstrict : @strict A E R_A B R_B f C con),
  forall n b1 e1 r e2, (forall b, r <> f b) -> trc R_A n (f b1,e1) (r,e2) ->
  exists n1 n2 r1 e1', trc R_B n1 (b1,e1) (con r1,e1') /\
      trc R_A n2 (f (con r1),e1') (r,e2) /\ (n1+n2 = n)%nat.
Proof.
intros. prep_trc. revert b1 e1 Heqp. induction H0;intros;subst.
  exfalso;injection Heqp;congruence.
specialize (IHtrc (eq_refl _)). destruct b.
pose proof (Hstrict _ _ _ _ H0) as H3. destruct H3 as [H3|H3];decompose record H3;clear H3;subst.
(* b1 was done *)
repeat eexists;eauto using done,step.
(* b1 took a step *)
specialize (IHtrc _ _ (eq_refl _)). decompose record IHtrc;clear IHtrc;subst.
repeat eexists;eauto using done,step with arith.
Qed.

Lemma plus_strict_l : forall e2, strict step_e step_e (fun e => plus e e2) con.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

Lemma plus_strict_r : forall x, strict step_e step_e (fun e => plus (con x) e) con.
Proof. unfold strict. intros. inversion H;subst;eauto. inversion H1. Qed.


Definition trc_inv : forall (A : Set) (R : A -> A -> Prop) (n : nat) (a b : A)
   (P : nat -> A -> A -> Prop),
   (a = b -> n = 0%nat -> P n a b) ->
   (forall b', R a b' -> forall n0, n = S n0 -> trc R n0 b' b -> P n a b) ->
   trc R n a b -> P n a b.
Proof. destruct 3;eauto. Qed.

Ltac refute_step := match goal with
  | [H : step_e (con _, _) _ |- _] => solve[inversion H]
  | [H : step_b (bcon _, _) _ |- _] => solve[inversion H]
  | [H : step_s (skip, _) _ |- _] => solve[inversion H]
  end.

Ltac split_trc H := inversion H;clear H;subst;[
  match goal with [H : _ = _ |- _] =>simplify_eq H;intros;subst end|try refute_step].

Ltac split_done_trc H :=
  inversion H using trc_inv;clear H;
    [let H:=fresh in intro H;injection H;clear H;intros;subst
    |let Hstep := fresh "Hstep" in intros ? Hstep;solve[inversion Hstep]].

Ltac split_unit_trc H :=
  match type of H with | @trc ?A ?R ?n _ _ =>
  inversion H using trc_inv;clear H;
    [discriminate || let H:=fresh in intro H;injection H;clear H;intros;subst
    |let Hstep := fresh "Hstep" in let Hrest := fresh "Hrest" in intros ? Hstep ? -> Hrest;
     (solve[inversion Hstep]||
     (inversion Hstep;subst;try refute_step;[idtac];
     try split_done_trc Hrest))];[idtac]
  end.

Ltac use_decompose T H :=
  apply strict_decompose with (1:=T) in H;[|discriminate];decompose record H;clear H;subst.

Lemma sound_e : forall P s Q, proof_e P s Q -> valid_e P s Q.
induction 1;unfold valid_e in * |- *;simpl;intros;
try match goal with [H : trc _ _ _ _ |- _] => split_unit_trc H;assumption end.
use_decompose (@plus_strict_l e2) H1. use_decompose (@plus_strict_r x1) H3. split_unit_trc H4. apply i. eauto.
eauto.
Qed.

Lemma inj_trc : forall {A A1:Set} (f : A -> A1) {R : A -> A -> Prop} {R1 : A1 -> A1 -> Prop}
   (H : forall x y, R x y -> R1 (f x) (f y)),
   forall n a b, trc R n a b -> trc R1 n (f a) (f b).
Proof. induction 2;subst;eauto using step,done. Qed.

Lemma inj_trc_fst : forall {A A1:Set} (f : A -> A1) {B : Set} {R : A*B -> A*B -> Prop} {R1 : A1*B -> A1*B -> Prop}
   (H : forall a1 b1 a2 b2, R (a1,b1) (a2,b2) -> R1 (f a1,b1) (f a2,b2)),
   forall n a1 b1 a2 b2, trc R n (a1,b1) (a2,b2) -> trc R1 n (f a1,b1) (f a2,b2).
Proof. intros. revert H0. apply (@inj_trc _ _ (fun x => (f (fst x), snd x)) R).
intros x y;destruct x,y;apply H. Qed.

Lemma inj_trc_fst' : forall {A:Set} (f : A -> A) {B : Set} {R : A*B -> A*B -> Prop}
   (H : forall a1 b1 a2 b2, R (a1,b1) (a2,b2) -> R (f a1,b1) (f a2,b2)),
   forall n a1 b1 a2 b2, trc R n (a1,b1) (a2,b2) -> trc R n (f a1,b1) (f a2,b2).
Proof. intros A f B R. eapply inj_trc_fst. Qed.

Lemma trc_trans : forall {A:Set} {R : A -> A -> Prop} {n1 a b},
  trc R n1 a b -> forall {n2 c}, trc R n2 b c -> trc R (n1+n2) a c.
Proof. induction 1;subst;simpl;eauto using step. Qed.

Ltac use_inj_trc :=
  match goal with [H : trc ?R1 _ (?e,?env0) _ |- trc ?R _ (?t,?env0) _] =>
     match t with context [e] => match eval pattern e at 1 in t with
       ?f e => apply (@inj_trc_fst _ _ f _ R1 R) in H;[|constructor(assumption)];
         eapply trc_trans;[eexact H|];clear H end end
  end.

(* For completeness, we use the Most General Triple (MGT) approach *)
Lemma mgt_e : forall (e : exp) (P : formula),
  proof_e P e (fun r env' => exists Z n, P Z /\ trc step_e n (e, Z) (con r, env')).
induction e;intro P;
try solve[eapply p_conseq_e_l;[constructor|];instantiate;simpl;firstorder;repeat eexists;eauto using @trc,step_e].
eapply p_plus;[apply IHe1|intro r;apply IHe2|]. clear;unfold impl;simpl;firstorder.
  repeat eexists;[eassumption|]. use_inj_trc. use_inj_trc. eapply step;[constructor(fail)|]. eauto using @trc.
Qed.

Lemma complete_e : forall (P : formula) (e : exp) (Q : Z -> formula),
  valid_e P e Q -> proof_e P e Q.
Proof. intros. eapply p_conseq_e_r. eapply mgt_e. simpl. firstorder. Qed.

Inductive proof_b : formula -> bexp -> (bool -> formula) -> Type :=
  | p_bcon : forall b Q, proof_b (Q b) (bcon b) Q
  | p_eql : forall P e1 Q1 e2 Q2,
      proof_e P e1 Q1 -> (forall r, proof_e (Q1 r) e2 (Q2 r)) ->
      proof_b P (eql e1 e2) (fun r e => exists r1 r2, r = Z.eqb r1 r2 /\ Q2 r1 r2 e)
  | p_le : forall P e1 Q1 e2 Q2,
      proof_e P e1 Q1 -> (forall r, proof_e (Q1 r) e2 (Q2 r)) ->
      proof_b P (le e1 e2) (fun r e => exists r1 r2, r = Z.leb r1 r2 /\ Q2 r1 r2 e)
  | p_not : forall P e Q, proof_b P e Q -> proof_b P (not e) (fun r => Q (negb r))
  | p_and : forall P e1 Q R, proof_b P e1 Q -> impl (Q false) (R false) -> forall e2, proof_b (Q true) e2 R
      -> proof_b P (and e1 e2) R
  | p_conseq_b : forall {A : Set} P' e Q', (forall (Z:A), proof_b (P' Z) e (Q' Z)) ->
       forall (P : formula) (Q : bool -> formula),
          (forall s v t, (forall Z, P' Z s -> Q' Z v t) -> (P s -> Q v t)) ->
       proof_b P e Q
  .

Lemma p_conseq_b_l : forall P' e Q, proof_b P' e Q ->
    forall (P : formula), (forall s, P s -> P' s) -> proof_b P e Q.
Proof. intros; apply (@p_conseq_b unit (fun _ => P') e (fun _ => Q));firstorder. Qed.

Lemma p_conseq_b_r : forall P e Q', proof_b P e Q' ->
    forall (Q : bool -> formula),
      (forall v t, Q' v t -> Q v t) -> proof_b P e Q.
Proof. intros; apply (@p_conseq_b unit (fun _ => P) e (fun _ => Q'));firstorder. Qed.

Lemma eql_strict_l : forall e2, strict step_b step_e (fun e => eql e e2) con.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

Lemma eql_strict_r : forall x, strict step_b step_e (fun e => eql (con x) e) con.
Proof. unfold strict. intros. inversion H;subst;eauto. inversion H1. Qed.

Lemma le_strict_l : forall e2, strict step_b step_e (fun e => le e e2) con.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

Lemma le_strict_r : forall x, strict step_b step_e (fun e => le (con x) e) con.
Proof. unfold strict. intros. inversion H;subst;eauto. inversion H1. Qed.

Lemma not_strict : strict step_b step_b not bcon.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

Lemma and_strict_l : forall e2, strict step_b step_b (fun e => and e e2) bcon.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

Lemma sound_b : forall P s Q, proof_b P s Q -> valid_b P s Q.
induction 1;unfold valid_b in * |- *;simpl;intros.
split_unit_trc H0.  assumption.
use_decompose (@eql_strict_l e2) H0. apply sound_e in p. specialize (p _ H _ _ _ H1). specialize (p0 x1).
   use_decompose (@eql_strict_r x1) H2. apply sound_e in p0. specialize (p0 _ p _ _ _ H0).
   split_unit_trc H3. repeat eexists. assumption.
use_decompose (@le_strict_l e2) H0. apply sound_e in p. specialize (p _ H _ _ _ H1). specialize (p0 x1).
   use_decompose (@le_strict_r x1) H2. apply sound_e in p0. specialize (p0 _ p _ _ _ H0).
   split_unit_trc H3. repeat eexists. assumption.
use_decompose not_strict H0. specialize (IHX _ H _ _ _ H1). split_unit_trc H2. destruct x1;assumption.
use_decompose (@and_strict_l e2) H0. specialize (IHX1 _ H _ _ _ H1).
   destruct x1;split_unit_trc H2;[specialize (IHX2 _ IHX1 _ _ _ Hrest)|apply i];assumption.
eauto.
Qed.      

Lemma mgt_b : forall (e : bexp) (P : formula),
  proof_b P e (fun r env' => exists n Z, P Z /\ trc step_b n (e, Z) (bcon r, env')).
Proof.
induction e;intro Z;repeat match goal with [e : exp |- _] => generalize (mgt_e e);revert e end;intros;
try (eapply p_conseq_b_r;[econstructor(intros;match goal with [H : context [?p _ ?e _] |- ?p _ ?e _] => apply H end)
 |instantiate;clear;simpl;firstorder;subst;repeat eexists;[eassumption|]
   ;repeat use_inj_trc;eauto using @trc,step_b]). 
eapply p_conseq_b_l. constructor. simpl. eauto 20 using @trc, step_b.
destruct v; eauto using @trc,step_b.
eapply p_and;[eapply IHe1| |eapply p_conseq_b_r;[apply IHe2|]];
  (clear;unfold impl;firstorder;repeat eexists;[eassumption|];repeat use_inj_trc;eauto using @trc,step_b).
Qed.

Lemma complete_b : forall (P : formula) (e : bexp) (Q : bool -> formula),
  valid_b P e Q -> proof_b P e Q.
Proof. intros. eapply p_conseq_b_r. eapply mgt_b. simpl. firstorder. Qed.

Inductive proof : formula -> stmt -> formula -> Type :=
  | p_assign : forall P Q x e, proof_e P e (fun v env => Q (set env x v)) -> proof P (assign x e) Q
  | p_skip : forall Q, proof Q skip Q
  | p_seq : forall P Q R s1 s2, proof P s1 Q -> proof Q s2 R -> proof P (seq s1 s2) R
  | p_cond : forall P b Q, proof_b P b Q ->
       forall s1 s2 R, proof (Q true) s1 R -> proof (Q false) s2 R -> proof P (cond b s1 s2) R
  | p_while : forall P Q b s,
       proof_b P b Q -> proof (Q true) s P -> proof P (while b s) (Q false)
  | p_conseq : forall {A : Type} P' s Q', (forall (Z:A), proof (P' Z) s (Q' Z)) ->
       forall (P Q : formula), (forall s t, (forall Z, P' Z s -> Q' Z t) -> (P s -> Q t)) ->
       proof P s Q
  .

Lemma p_conseq_l : forall P' s Q, proof P' s Q ->
    forall (P : formula), (forall s, P s -> P' s) -> proof P s Q.
Proof. intros; apply (@p_conseq unit (fun _ => P') s (fun _ => Q));firstorder. Qed.
Lemma p_conseq_r : forall P s Q', proof P s Q' ->
    forall (Q : formula), (forall t, Q' t -> Q t) -> proof P s Q.
Proof. intros; apply (@p_conseq unit (fun _ => P) s (fun _ => Q'));firstorder. Qed.


Lemma assign_strict : forall x, strict step_s step_e (assign x) con.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

Lemma seq_strict_l : forall s2, strict step_s step_s (fun s1 => seq s1 s2) (fun _:unit => skip).
Proof. unfold strict. intros. pose tt. inversion H;subst;eauto. Qed.

Lemma cond_strict : forall s1 s2, strict step_s step_b (fun b => cond b s1 s2) bcon.
Proof. unfold strict. intros. inversion H;subst;eauto. Qed.

(* while takes a bit more work to express how complete trace decomposes.
   In particular, we introduce a new inductive type to demonstrate that
   there are a finite number of loop iterations *)
Inductive while_trace b s env : Env -> Prop :=
 | while_done : forall n env', trc step_b n (b,env) (bcon false,env') -> while_trace b s env env'
 | while_step : forall n1 env1, trc step_b n1 (b,env) (bcon true,env1) ->
     forall n2 env2, trc step_s n2 (s,env1) (skip,env2) ->
     forall env3, while_trace b s env2 env3 -> while_trace b s env env3.

Lemma while_dec : forall n b s env env', trc step_s n (while b s,env) (skip,env') -> while_trace b s env env'.
intro n. pattern n. apply (well_founded_induction lt_wf). clear n.
intros.
split_trc H0. inversion H1;subst.
use_decompose (@cond_strict (seq s (while b s)) skip) H2.
split_trc H3. inversion H2;subst;try refute_step;clear H2.
destruct x1.
(* making another loop *)
use_decompose (@seq_strict_l (while b s)) H4. split_unit_trc H3.
   apply H in Hrest. eapply while_step;eassumption. omega.
(* finishing here *)
split_unit_trc H4. eapply while_done;eassumption.
Qed.

Lemma sound_s : forall P s Q, proof P s Q -> valid_s P s Q.
induction 1;unfold valid_s in * |- *;intros;
repeat match goal with [H : proof_e _ _ _ |- _] => apply sound_e in H
                     | [H : proof_b _ _ _ |- _] => apply sound_b in H end.
* use_decompose (@assign_strict x) H0. split_unit_trc H2. eauto.
* split_unit_trc H0. assumption.
* use_decompose (@seq_strict_l s2) H0. 
  specialize (IHX1 _ H _ _ H1);clear H H1. split_trc H2. inversion H;subst;[|solve[inversion H5]]. eauto.
* use_decompose (@cond_strict s1 s2) H0. specialize (p _ H _ _ _ H1); clear H H1.
  split_trc H2. inversion H;subst;[|solve[inversion H6]]. destruct x1;eauto.
* apply while_dec in H0. induction H0;eauto.
* eauto.
Qed.

Lemma mgt_s_while_form : forall b s,
  (forall (P : formula), proof (fun env => forall n env', trc step_s n (while b s,env) (skip,env') -> P env')
                   (while b s) P)
  ->
  (forall P, proof P (while b s) (fun env' : Env =>
                 exists n Z, P Z /\ trc step_s n (while b s, Z) (skip, env'))).
Proof. intros. eapply p_conseq_l. apply X. clear;simpl;firstorder. Qed.

Ltac finish_mgt := clear;unfold impl;simpl;firstorder;subst;repeat eexists;[eassumption|];
  repeat use_inj_trc;eauto 20 using @trc,step_e,step_b,step_s.

Lemma mgt_s : forall (s : stmt) (P : formula),
  proof P s (fun env' => exists n Z, P Z /\ trc step_s n (s, Z) (skip, env')).
induction s;intro P;repeat match goal with
 | [e : exp |- _] => generalize (mgt_e e);revert e
 | [b : bexp |- _] => generalize (mgt_b b);revert b
end;intros.
* constructor. eapply p_conseq_e_r. eapply X. finish_mgt.
* eapply p_conseq_r. constructor. finish_mgt.
* eapply p_seq. eapply IHs1. eapply p_conseq_r. eapply IHs2. finish_mgt.
* eapply p_cond. eapply X. eapply p_conseq_r. eapply IHs1. finish_mgt. eapply p_conseq_r. eapply IHs2. finish_mgt.
* revert P. apply mgt_s_while_form. intro P.
  apply p_while with (Q:=fun (v:bool) => if v then fun t => (forall n env',
          trc step_s n (seq s (while b s),t) (skip,env') -> P env') else P).
     eapply p_conseq_b_r. apply X. clear;simpl;firstorder.
       destruct v;intros;eapply H;(eapply step;[constructor|]);use_inj_trc;eauto using @trc,step_s.
     eapply p_conseq_r. apply IHs. clear;simpl;firstorder. eapply H. use_inj_trc;eauto using @trc,step_s.
Qed.

Lemma complete : forall P e Q, valid_s P e Q -> proof P e Q. 
Proof. intros. eapply p_conseq_r. apply mgt_s. firstorder. Qed.