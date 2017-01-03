(*******************************************************************)
(*  This is part of CAWU, it is distributed under the terms        *)
(*    of the GNU Lesser General Public License version 3           *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2016: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * Example: CCS *)

Require Import "../himp/examples/ex03_list/ho_proof_gen".
Require Import "../himp/examples/ex03_list/step_ok".
Require Import List.


Set Implicit Arguments.

Module Type N.
 Parameter N: Set.           (* channels names *)
End N.

Module CCS(Export M: N).


 (** CCS labels (or prefixes, they are the same) *)
 Inductive label := tau | out(a: N) | inp(a: N).
  
 (** CCS processes. Instead of using process constants, as in the paper, 
   we use coinductive definition. In other words, we will use Coq's corecursive 
   definitions to encode CCS recursion *)
 CoInductive S :=
 | snil
 | prf(l: label)(p: S)
 | pls(p q: S)
 | par(p q: S)
 | new(a: N)(p: S)
 | rep(p: S).

 Inductive cfg : Set :=
   Cfg {proc:S}.

 (** when a name [a] does not appear in a label [l] *)
 Definition fresh a (l: label) :=
   match l with tau => True | out b | inp b => a<>b end.

 (** the (standard) LTS  *)
 CoInductive trans: S -> label -> S -> Prop :=
 | t_prf: forall l p, trans (prf l p) l p
 | t_pls_l: forall p q l p', trans p l p' -> trans (pls p q) l p'
 | t_pls_r: forall p q l q', trans q l q' -> trans (pls p q) l q'
 | t_par_l: forall p l p' q, trans p l p' -> trans (par p q) l (par p' q)
 | t_par_r: forall p l p' q, trans p l p' -> trans (par q p) l (par q p')
 | t_par_lr: forall a p p' q q', trans p (out a) p' -> trans q (inp a) q' -> trans (par p q) tau (par p' q')
 | t_par_rl: forall a p p' q q', trans p (inp a) p' -> trans q (out a) q' -> trans (par p q) tau (par p' q')
 | t_new: forall a p l p', trans p l p' -> fresh a l -> trans (new a p) l (new a p')
 | t_rep: forall p l p', trans (par (rep p) p) l p' -> trans (rep p) l p'
 .
 Hint Resolve t_prf t_par_l t_par_r t_par_lr t_par_rl t_new t_pls_l t_pls_r.

 Inductive ccs_step: cfg -> cfg -> Prop :=
 | proc_step : forall p l q, trans p l q -> ccs_step (Cfg p) (Cfg q).

End CCS.

Module acd.
  Inductive N': Type := a | c | d.
  Definition N := N'.
End acd.

Module Import CCSacd := CCS(acd).


(** The four processes from Section 4 *)
CoFixpoint A := prf (inp a) (prf (inp c) D)
      with B := prf (inp a) (prf (inp c) C)
      with C := prf (out a) (par A C)
      with D := prf (out a) (par B D).

Print reaches.

CoFixpoint testCCS := forall (A : S), (prf (inp a) A).

Definition my_cfg : cfg := (Cfg A).

Inductive my_spec : Spec cfg :=
| my_spec_const : forall x, my_spec (Cfg (prf (inp x) A)) (eq (Cfg A)).

Require Import "../common/proof".
Lemma test : sound ccs_step my_spec.
Proof.
  unfold sound. intro;intros. inversion H;subst. eapply proved_sound with my_spec.
  intros. inversion H0; subst. apply sstep with (Cfg A). econstructor. econstructor.
  constructor. trivial. assumption.
Qed.

Print sound.

Definition blah := my_spec my_cfg (eq my_cfg).
Print blah.

Print my_cfg.

Lemma test : reaches ccs_step (Cfg A my_list) (eq (Cfg A my_list)).
Proof.
  

 
 (** dumb utilities for corecursion *)
 Definition id_S(p: S): S :=
   match p with
   | snil => snil
   | prf l p => prf l p
   | new a' p => new a' p
   | par p q => par p q
   | pls p q => pls p q
   | rep p => rep p 
   end.
 Lemma Sd p: p = id_S p.
 Proof. now case p. Qed.                  

 (** the function defining simulations and similarity *)
 Program Definition s: mon (S -> S -> Prop) :=
   {| body R p q :=
        forall l p', trans p l p' -> exists2 q', trans q l q' & R p' q' |}.
 Next Obligation. cbv. firstorder. Qed.
 
 (** the symmetrised version, defining bisimulations and bisimilarity *)
 Notation b := (cap s (converse o s o converse)).

 Infix "~" := (gfp b) (at level 70).
 Notation B := (B b).
 Notation T := (t B).
 Notation t := (t b).

 (** Some valid laws  *)
 Lemma parC: forall p q, par p q ~ par q p.
 Proof.
   coinduction R H. intros p q; split. 
   intros l p' pp'. inversion_clear pp'; eauto.
   intros l q' qq'. simpl. inversion_clear qq'; eauto.
 Qed.

 Lemma parA: forall p q r, par p (par q r) ~ par (par p q) r.
 Proof.
   coinduction R H. intros p q r; split. 
   intros l p' pp'. inversion_clear pp'; eauto.
    inversion_clear H0; eauto. 
    inversion_clear H1; eauto. 
    inversion_clear H1; eauto. 
   intros l q' qq'. simpl. inversion_clear qq'; eauto.
    inversion_clear H0; eauto. 
    inversion_clear H0; eauto. 
    inversion_clear H0; eauto. 
 Qed.
 
 Lemma par0p: forall p, par nil p ~ p.
 Proof.
   coinduction R H. intro p. split.
   intros l p0 pp0. inversion_clear pp0.
    inversion H0.
    eauto. 
    inversion H0. 
    inversion H0. 
   intros l p' pp'. exists (par nil p'). auto. apply H. 
 Qed.

 
 (** * Equivalence closure *)
 
 (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
 Lemma refl_t: const eq <= t.
 Proof.
   apply leq_t. intro. change (eq <= b eq).
   apply cap_spec. split. 
    intros p q <- ? p'; eauto.
    intros p q <- ? p'; eauto.
 Qed.

 (** converse is compatible *)
 Lemma converse_t: converse <= t.
 Proof. apply invol_t. Qed.

 (** so is squaring *)
 Lemma square_t: square <= t.
 Proof.
   apply Coinduction, by_Symmetry. 
   intros R x z [y xy yz]. now exists y.
   rewrite cap_l at 1. rewrite <-id_t. 
   intros R x z [y xy yz] l x' xx'.
   destruct (xy _ _ xx') as [y' yy' x'y']. 
   destruct (yz _ _ yy') as [z' zz' y'z'].
   exists z'. assumption. eexists; eassumption.
 Qed.

 (** thus bisimilarity, [t R], and [T f R] are always equivalence relations *)
 Global Instance Equivalence_T f R: Equivalence (T f R).
 Proof. apply Equivalence_T. apply refl_t. apply converse_t. apply square_t. Qed.
 Global Instance Equivalence_t R: Equivalence (t R).
 Proof. apply Equivalence_t. apply refl_t. apply converse_t. apply square_t. Qed.
 Corollary Equivalence_bisim: Equivalence (gfp b).
 Proof Equivalence_t bot.

 (** * Context closure *)

 (** ** prefix *)
 Lemma prf_t a: unary_ctx (prf a) <= t.
 Proof.
   assert (H: unary_ctx (prf a) <= s).
    intro R. apply leq_unary_ctx. intros p q Hpq.
    intros l p' pp'. inversion pp'. subst; eauto. 
   apply Coinduction, by_Symmetry. apply unary_sym.
    rewrite H at 1. now rewrite <-b_T.
 Qed.
 Global Instance prft_t a: forall R, Proper (t R ==> t R) (prf a) := unary_proper (@prf_t a).

 (** ** name restriction *)
 Lemma new_t a: unary_ctx (new a) <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply unary_sym.
   intro R. apply (leq_unary_ctx (new a)). intros p q Hpq l p0 Hp0.
   inversion_clear Hp0. destruct (proj1 Hpq _ _ H) as [???]. eexists. eauto.
   apply (id_t B). now apply in_unary_ctx.
 Qed.
 Global Instance newt_t a: forall R, Proper (t R ==> t R) (new a) := unary_proper (@new_t a).

 (** ** choice *)
 Lemma pls_t: binary_ctx pls <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply binary_sym.
   intro R. apply (leq_binary_ctx pls).
   intros p q Hpq r s Hrs l p0 Hp0. inversion_clear Hp0.
   destruct (proj1 Hpq _ _ H) as [? ? ?]. eexists. eauto. now apply (id_T b).
   destruct (proj1 Hrs _ _ H) as [? ? ?]. eexists. eauto. now apply (id_T b).
 Qed.
 Global Instance plst_t: forall R, Proper (t R ==> t R ==> t R) pls := binary_proper pls_t.
 
 (** ** parallel composition *)
 (** Lemma 8.1 *)
 Lemma par_t: binary_ctx par <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply binary_sym.
   intro R. apply (leq_binary_ctx par).
   intros p q Hpq r s Hrs l p0 Hp0. inversion_clear Hp0.
    destruct (proj1 Hpq _ _ H) as [? ? ?]. eexists. eauto.
    apply (fTf_Tf b). apply (in_binary_ctx par). now apply (id_T b). now apply (b_T b). 
    destruct (proj1 Hrs _ _ H) as [? ? ?]. eexists. eauto.
    apply (fTf_Tf b). apply (in_binary_ctx par). now apply (b_T b). now apply (id_T b). 
    destruct (proj1 Hpq _ _ H) as [? ? ?].
    destruct (proj1 Hrs _ _ H0) as [? ? ?]. eexists. eauto.
    apply (fTf_Tf b). apply (in_binary_ctx par); now apply (id_T b).     
    destruct (proj1 Hpq _ _ H) as [? ? ?].
    destruct (proj1 Hrs _ _ H0) as [? ? ?]. eexists. eauto.
    apply (fTf_Tf b). apply (in_binary_ctx par); now apply (id_T b).     
 Qed.
 Global Instance part_t: forall R, Proper (t R ==> t R ==> t R) par := binary_proper par_t.
 
 (** ** replication (the challenging operation) *)

 (** preliminary results *)
 Lemma unfold_rep p: rep p ~ par (rep p) p.
 Proof.
   coinduction R H. clear H. split.
   intros l p' pp'. inversion_clear pp'.
   eexists. eassumption. reflexivity.
   simpl. intros l p' pp'. eexists. constructor; eassumption.
   reflexivity.
 Qed.

 (** Proposition 8.2(i) *)
 Proposition rep_trans p l p0: trans (rep p) l p0 -> exists2 p1, trans (par p p) l p1 & p0 ~ par (rep p) p1.
 Proof.
   remember (rep p) as rp. intro H. revert rp l p0 H p Heqrp. fix 4.
   intros rp l p0 H p E. destruct H; try discriminate.
   remember (par (rep p0) p0) as rpp. destruct H; try discriminate. 
    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. eexists. eauto. 
    rewrite H1. now rewrite (parC (rep _)), <-parA, <-unfold_rep.
    
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. eexists. eauto.
    now rewrite parA, <-unfold_rep.
    
    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. 
    inversion H1; subst; clear H1; (eexists; [eauto|]).
    rewrite H2. now rewrite (parC p'0), parA, <-unfold_rep, (parC q'), parA. 
    rewrite H2. now rewrite parA, <-unfold_rep, (parC q'), parA.

    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. 
    inversion H1; subst; clear H1; (eexists; [eauto|]).
    rewrite H2. now rewrite (parC p'0), parA, <-unfold_rep, parA. 
    rewrite H2. now rewrite parA, <-unfold_rep, parA.
 Qed.

 (** Proposition 8.2(ii) *)
 Proposition rep_trans' p l p1: trans (par p p) l p1 -> exists2 p0, trans (rep p) l p0 & p0 ~ par (rep p) p1.
 Proof.
   assert (E: par (rep p) (par p p) ~ rep p).
    now rewrite parA, <-2unfold_rep.
   intros H.
   assert (H': trans (par (rep p) (par p p)) l (par (rep p) p1)) by auto.
   destruct (proj1 (gfp_pfp b _ _ E) _ _ H'). eexists. eauto. symmetry. assumption.
 Qed.

 (** Lemma 8.4 
     (note that we do not need Lemma 8.3 as in the paper: we
     use instead the more general fact that we can reason up to
     equivalence [Equivalence_t] and that [~ <= t R]) *)
 Lemma rep_t: unary_ctx rep <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply unary_sym.
   intro R. apply (leq_unary_ctx rep). intros p q Hpq l p0 Hp0.
   apply rep_trans in Hp0 as [p1 ppp1 p0p1]. 
   assert (H: b (t R) (par p p) (par q q)).
    apply (compat_t b). apply par_t. now apply in_binary_ctx. 
   destruct (proj1 H _ _ ppp1) as [q1 qqq1 p1q1].
   apply rep_trans' in qqq1 as [q0 Hq0 q0q1].
   eexists. eassumption.
   rewrite p0p1, q0q1.
   apply (ftT_T _ par_t). apply (in_binary_ctx par). 
    apply (fTf_Tf b). apply (in_unary_ctx rep). now apply (b_T b).
    now apply (t_T b). 
 Qed.
 Global Instance rept_t: forall R, Proper (t R ==> t R) rep := unary_proper rep_t.
 
End CCS.

(** * A proof by enhance coinduction  *)

Module acd.
 CoInductive N': Type := a | c | d.
 Definition N := N'.
End acd.
Module Import CCSacd := CCS(acd).

(** The four processes from Section 4 *)
CoFixpoint A := prf (inp a) (prf (inp c) D)
      with B := prf (inp a) (prf (inp c) C)
      with C := prf (out a) (par A C)
      with D := prf (out a) (par B D).

Lemma dA: A = prf (inp a) (prf (inp c) D).
Proof. apply Sd. Qed.
Lemma dB: B = prf (inp a) (prf (inp c) C).
Proof. apply Sd. Qed.
Lemma dC: C = prf (out a) (par A C).
Proof. apply Sd. Qed.
Lemma dD: D = prf (out a) (par B D).
Proof. apply Sd. Qed.

(** Utilities to factor code thanks to the (relative) determinism of the considered processe *)
Lemma bAB (R: S -> S -> Prop): R (prf (inp c) D) (prf (inp c) C) -> b R A B.
Proof. intro. rewrite dA, dB. split; intros ? ? T; inversion_clear T; eauto. Qed.
Lemma bCD (R: S -> S -> Prop): R (par A C) (par B D) -> b R C D.
Proof. intro. rewrite dC, dD. split; intros ? ? T; inversion_clear T; eauto. Qed.

(** the proof by enhanced bisimulation *)
Goal cup (pair A B) (pair C D) <= gfp b.
Proof.
  apply coinduction. apply cup_spec. split; apply ->leq_pair. 
  apply bAB. apply prft_t. symmetry. apply (id_t b). apply <-leq_pair. apply cup_r.
  apply bCD. apply part_t; apply (id_t b); apply <-leq_pair. apply cup_l. apply cup_r.
Qed.
