Set Implicit Arguments.

Ltac intro_til tac := tac || (intro ; intro_til tac).

(* This file explores extensively different properties
   we might expect to hold of derived rules,

   though only for the exists-path system.
 
 There's a property "derived valid" which is just based on the assumption about
 your rules that comes up most naturally when trying to prove that
 stable (derived F X) assuming subrel X (stepF (derived F X)).

 However, proving derived_valid F lets you in places inspect terms
 of type derived F X, which lets you justify rules whose proof may
  depend critically on that being the only derived rule used.
 (is this even a semantic possibility?)
 
 derived_valid' generalizes over F in these results in the most stupid
 way to allow any set G of derived rules which expands on F.
 Under the assumption that F is monotone (subrel S T -> subrel (F S) (F T)),
 derived_valid and two successively simpler properties,
 derived_valid'' are all equivalent.

 Also defined monotonize, which is the smallest (pointwise) monotonic
 operator extending F, and showed that
 derived_valid' F <-> derived_valid' (monotonize F).

 To complete a chain like derived_valid' F <-> derived_valid''' (monotinize F),
 would need something like derived_valid' (monotonize F) -> derived_valid' F.
 
 -- one note is that the mendler-style stuff in derived means that F can't
    effectively depend on things being NOT in the argument relation,
   so we ought to be able to prove
   derived F X x P <-> derived (monotonize F) X x P.
  Not sure how that fits with soundness conditions.
  Guess that at least says something in the fully semantic derived_valid_0...

  Ahh, that means derived assumes by itself that F is "w.l.o.g" mono.

  and, under assumption that F in mono_op, we can show also the 
  derived_valid that makes no special provisions is equivalent to all of the
  above, and also an inlined version of derived_valid,

  Definition derived_valid_m (F : RRel -> RRel) : Prop :=
    forall (X : RRel), subrel (F (stepF (derived F X))) (stepF (derived F X)).

  The simplest looking of the rules is
  Definition derived_valid''' (F : RRel -> RRel) : Prop :=
    forall (X : RRel), subrel (F (stepF X)) (stepF (derived F X)).
  but in practice derived_valid_m seems to be even easier to prove, because
  if F Q has children of Q, the cildren are already in the form stepF (derived F X),
  so the proof (automation) doesn't have to figure out how to lift stepF X into
  stepF (derived X) (though maybe registering a lemma to that effect could help).

  Because of this equivalence of all the different version, under assumptions of
  monotonicity, we can freely combine any sets of valid operators!
 *)

Module Type language.
Parameter cfg : Set.
Parameter step : cfg -> cfg -> Prop.
End language.

Module Cotrans(L : language).

Import L.

(* Type of reachability relations: if X x P holds for
   X : RRel, say  "X claims x reaches P" *)
Definition RRel : Type := cfg -> (cfg -> Prop) -> Prop.

(* Being a subrelation *)
Definition subrel (A B : RRel) : Prop := forall x P, A x P -> B x P.
Lemma subrel_trans (P Q R : RRel) :
  subrel P Q -> subrel Q R -> subrel P R.
Proof. firstorder. Qed.
Lemma subrel_refl (P : RRel) : subrel P P.
Proof. firstorder. Qed.

(* Some starting tactics for proving with subrel *)
Create HintDb subrel discriminated.
Hint Resolve subrel_refl subrel_trans : subrel.
(* 
Hint Extern 4 (subrel ?P ?Q) =>
  match goal with
  | [H : subrel P ?M |- _] => refine (subrel_trans H _) 
  | [H : subrel ?M ?Q |- subrel ?P ?Q] => refine (subrel_trans _ H)
  end
  : subrel.
  *)


Ltac fold_subrel :=
  match goal with [|- forall x P, ?R1 x P -> ?R2 x P] => fold (subrel R1 R2) end.
(* If the goal is to show that a particular x P is included in a relation,
   and the only thing we know about (x,P) is that it's included in another
   relation, it must be a subrel problem *)
Ltac by_subrel :=
match goal with [HxP : ?S ?x ?P |- ?T ?x ?P ] =>
   revert x P HxP; fold (subrel S T)
end.

(* Defining actual reachability. *)
CoInductive reaches (x : cfg) (P : cfg -> Prop) : Prop :=
  | Done : P x -> reaches x P
  | Step : forall y, step x y -> reaches y P -> reaches x P
  .
(* The rest of the game is to define the reachabiliy relation
   corresponding to the specific claims we make about a program,
   and somehow show it's a subset of the true claims *)
Definition sound (X : RRel) : Prop := subrel X reaches.

(* To do this we'll use coinduction, based on showing that
   reaches is the greatest fixpoint of this operator that
   transforms reachability relations *)
Inductive stepF (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | DoneF : P x -> stepF X x P
  | StepF : forall y, step x y -> X y P -> stepF X x P.
(* First, prove reaches is a fixpoint of stepF *)
Lemma reaches_unfold : subrel reaches (stepF reaches).
destruct 1;econstructor(eassumption).
Qed.
Lemma reaches_fold : subrel (stepF reaches) reaches.
destruct 1;econstructor(eassumption).
Qed.
(* Second, that it's the greatest fixpoint.
   It's actually greater than any set X with subrel X (stepF X).
   In other words, any stepF-stable set is sound.
   *)
Definition stable (X : RRel) : Prop := subrel X (stepF X).
CoFixpoint stable_sound X (Hstable : stable X) : sound X :=
  fun x P HxP =>
  match Hstable _ _ HxP with
  | DoneF Px => Done _ _ Px
  | StepF y Rxy XyP => Step Rxy (@stable_sound _ Hstable _ _ XyP)
  end.

(* Fixpoints are only guaranteed to exists for montone operators. *)
Definition mono (F : RRel -> RRel) : Prop :=
  forall (S T : RRel), subrel S T -> subrel (F S) (F T).
Lemma by_mono (F : RRel -> RRel) (S T : RRel) :
  mono F -> subrel S T -> subrel (F S) (F T).
Proof. auto. Qed.

(* The operator stepF is in fact monotonic *)
Lemma stepF_mono : mono stepF.
  (* or, (P Q : RRel) : subrel P Q -> subrel (stepF P) (stepF Q). *)
unfold subrel; induction 2;eauto using stepF.
Qed.
Hint Resolve by_mono stepF_mono : subrel.

(* Constructing a set that's directly stable in this sense
   is quite tedious because everything has to be supported
   after one step -
     if you make any claim (x,P), you must also explicitly
     make a claim (y,P) for some immediate successor y of x.

  Proving something about each claim of X consists of
  showing that X is a subset of some set.

  In the most general notion, we'd have an operator
  (F : RRel -> RRel), such that proving X is stable
  under F implies it's sound: subrel X (F X) -> subrel X reaches.

TODO:
  Getting more specific, without having seriously analysed
  the general form, we'll think of "derived rules" as monotone
  functions that compute the set of claims that are immediate
  consequences of a starting set of claims, construct
  an operator "derived" that closes an initial set of
  claims under a rule, and consider when the result is stable.
  By construction we'll have

  X `subrel` derived F X

  So when we do have

  derived F X `subrel` stepF (derived F X)

  we also have

  X `subrel` reaches.

  By transitivity, a necessary condition for the
  derived set to be stable is that

  X `subrel` F X `subrel` stepF (F X).

  To be a good rule, so only have to reason about
  claims contained in X, this should also be sufficient.

  In a bit more detail, dervied starts with the operator F,
  and find the least fixpoint of (stepF + F) which is greater than X -
  in other words, the least fixpoint of (stepF + F + const X).

  stepF is included because it should always be sound.

  See fixpoints.v for generic constructions and results about
  fixpoints, which we don't use here.
 *)

(* Uses Mendler style in drule', becuase F (derived F X) x P
   is a non-strictly-positive occurance of derived *)
Inductive derived (F : RRel -> RRel)
                   (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dleaf : X x P -> derived F X x P
  | ddone : P x -> derived F X x P
  | dstep : forall y, step x y -> derived F X y P -> derived F X x P
  | drule' : forall Q, subrel Q (derived F X) -> F Q x P -> derived F X x P.
Definition drule F X : forall x P, F (derived F X) x P -> derived F X x P :=
(* or, forall F X, subrel (F (derived F X)) (derived F X) *)
 fun x P => drule' x P (fun _ _ H => H).
(* And basic monotonicity properties, that derived is
   monotone in both X and F *)
Lemma deri_mono : forall F P Q, subrel P Q -> subrel (derived F P) (derived F Q).
unfold mono; intros. unfold subrel in H.
induction 1;eauto using derived, drule.
Qed.
Lemma deri_lift (F G : RRel -> RRel)
  (Hlift : forall X, subrel (F X) (G X)) :
  forall X, subrel (derived F X) (derived G X).
unfold subrel; induction 1;eauto using derived.
apply (drule' _ _ H0). by_subrel;eauto with subrel.
Qed.
Hint Resolve deri_mono deri_lift : subrel.

(* For the fixpoint to be well-defined, we might expect to requrie
   that F monotone, but the mendler-style recursion effectively
   monotonizes F, by letting us pick a smaller Q if it makes a difference.
   A few lemmas demonstrating this.

  The main upside of this is that when considering valitity conditions,
  we might as well assume that F is monotone if it helps prove anything.

  To show this, we define how monotonize, and show
  derived F X is equivalent to derived (monotonize F X)
  *)
(* This is the minimal monotonic extension of a relation transformer *)
Inductive monotonize (F : RRel -> RRel) (X : RRel) (x : cfg) (P : cfg -> Prop)
 : Prop := | m_mono : forall Y, F Y x P -> subrel Y X -> monotonize F X x P. 
(* Proving it's actually correct: 1) monotonic *)
Lemma monotonize_mono F : mono (monotonize F).
destruct 2.
econstructor;[eassumption|];instantiate;eauto with subrel.
Qed.
(* 2) includes F *)
Lemma monotonize_includes F :
 forall X, subrel (F X) (monotonize F X).
econstructor;[eassumption|];instantiate;auto with subrel.
Qed.
(* 3) Is smaller than any other monotone relation which F *)
Lemma monotonize_min F : 
   (forall (G : RRel -> RRel),
      mono G ->
      (forall X, subrel (F X) (G X)) ->
      (forall X, subrel (monotonize F X) (G X))).
destruct 3. apply H in H2. by_subrel;eauto with subrel.
Qed.
(* A further property *)
Lemma monotonize_pointwise F G:
  (forall X, subrel (F X) (G X)) ->
  (forall X, subrel (monotonize F X) (monotonize G X)).
unfold subrel. destruct 2. eapply m_mono;eauto.
Qed.

(* Now actually prove derived ignores whether F is mono *)
Lemma derived_wlog_mono (F : RRel -> RRel) :
  forall X x P, derived (monotonize F) X x P <-> derived F X x P.
Proof.
split;induction 1;eauto using derived.
(* forward *)
destruct H1.
apply drule' with Y;eauto with subrel.
(* backward *)
apply drule; eauto using monotonize.
Qed.

(* Now a few properties about derived, for reasoning about the
   generated relation *)

(* by construction, derived is closed under step *)
Lemma deri_step :
   forall F X x P, stepF (derived F X) x P -> derived F X x P.
   (* kept open so auto can more easily use it pointwise *)
destruct 1;eauto using derived.
Qed.
Lemma deri_step_subrel :
   forall F X, subrel (stepF (derived F X)) (derived F X).
   (* and folded for subrel goals *)
destruct 1;eauto using derived.
Qed.
Lemma drule_subrel :
   forall F X Q,
     subrel Q (derived F X) ->
     subrel (F Q) (derived F X).
unfold subrel;eauto using derived.
Qed.
Lemma dleaf_subrel : forall F X, subrel X (derived F X).
unfold subrel;eauto using derived.
Qed.

Hint Resolve deri_step_subrel drule_subrel : subrel.
(* combining deri_step and dleaf, used in a few places *)
Lemma deri_incl_step F X : subrel (stepF X) (derived F X).
unfold subrel;destruct 1;eauto using derived.
Qed.
(* closing a set again adds no additional conclusions.
   This is useful in combination with deri_lift to
   prove lemmas about combining sets of rules *)
Lemma deri_join : forall F X x P, derived F (derived F X) x P -> derived F X x P.
induction 1;eauto using derived.
Qed.
Lemma deri_join_subrel : forall F X, subrel (derived F (derived F X)) (derived F X).
exact deri_join.
Qed.

(* this is the notion of a set X having a proof which uses rules F. *)
Definition derived_stable F X := subrel X (stepF (derived F X)).

(* Now consider various validity conditions.
   Beyond simply ensuring validity of a single set of rules,
   we would like to find composable conditions.
 *)

(* First, the most direct statement of validity as a derived rule *)
Definition validity_definition (F : RRel -> RRel) : Prop :=
  forall (X : RRel),
    derived_stable F X -> stable (derived F X).

(* TODO:
   Perhaps we can eliminate X:
   by using the derived_stable assumption to unfold it,
   derived_stable F X implies
   X `subset` stepF(gfp (F^* (stepF (-)))).
   Maybe some condition on F and this set is
   equivalent?

   derived_valid implies
   F (gfp (stepF (F^* -))) <= gfp (stepF (F^* -)),
   which in turn implies that F reaches <= reaches.
   Don't see that that implies back to any of the
   validity conditions
   (though I think it does ensure soundness)
   Also doesn't seem to combine freely.
   Certainly have example (where relation has some
     initial states, and some sets they don't reach,
     so theres's a set Initial of false claims about
     initial points)
   where reaches is F-closed and G-closed,
    and gfp (step o F^* ) = gfp (step o G^* ) = gfp ste
    but gfp (step o (F+G)* ) is step (universe)
   (F X = X when X <= gfp step, X + Initial otherwse,
    G X = X when X disjoint from Initial, U otherwise)
   *)
(* By trying to prove forall F, validity_definition F
   by induction on the (derived F X) from stable,
   we see the leaf/done/step cases can be handled independently
   of F, leaving a case equivalent to this*)
Definition derived_valid_case (F : RRel -> RRel) : Prop :=
  forall X, subrel X (stepF (derived F X)) ->
  forall Q, subrel Q (stepF (derived F X)) ->
    subrel (F Q) (stepF (derived F X)).

(* These are in fact equivalent *)
Lemma validity_equivalence : forall F,
  (validity_definition F <-> derived_valid_case F).
unfold validity_definition,derived_valid_case.
split;intros.
apply H in H0; eauto with subrel.
induction 1; eauto using stepF. by_subrel;eauto with subrel.
Qed.

(* Assuming monotonicity, we might as well set Q to it's upper bound *)
Definition derived_valid (F : RRel -> RRel) : Prop :=
  forall X, subrel X (stepF (derived F X)) ->
    subrel (F (stepF (derived F X))) (stepF (derived F X)).

(* this is obviously equivalent *)
Lemma drop_Q : forall F, mono F ->
  (derived_valid_case F <-> derived_valid F).
unfold derived_valid_case, derived_valid.
Proof. firstorder. Qed.

(* It seems strange to need the assumption about X in derived_valid -
   it's not guaranteed a value (derived F X) x P even actually contains
   a dleaf case so a proof derived_valid_case F can hardly assume it
   happens, and if it does occur, assumption about X can be wrapped up
   into derived F X by dleaf for use on the right hand side.

   Perhaps a rule that somehow throws away progress could use that
   hypothesis to unfold to stepF (stepF (derived F X)) or even more.

   Anyway, I haven't been able to show equivalence or find a counterexample,
   and the simpler definition is easily proved for all the imporant rules.
   
   Also, that hypothesis, by fixing the set of rules used in the proof of X,
   gets in the way of compositionality.
 *)
Definition derived_valid_m (F : RRel -> RRel) : Prop :=
  forall (X : RRel), subrel (F (stepF (derived F X))) (stepF (derived F X)).

(* This is obviously stronger *)
Lemma valid_m_stronger : forall F, derived_valid_m F -> derived_valid F.
Proof. firstorder. Qed.

Lemma deri_sound F (Hvalid : validity_definition F)
                 X (X_stable : derived_stable F X) :
                 sound X.
intros x P HxP;apply stable_sound with (derived F X);auto using dleaf.
Qed.

Lemma validity_from_m : forall F, mono F -> derived_valid_m F -> validity_definition F.
intros.
apply validity_equivalence.
apply drop_Q. assumption.
apply valid_m_stronger.
assumption.
Qed.

Module OverlySemanticNonsense.
(* There's actually an even more semantical statement,
    derived_stable F X -> sound X,
   but it doesn't contribute much - any proof of that basically
   has to apply coinduction itself to show X is in reaches,
   meaning it either finds a stable superset some other way than
   constructing derived F X, or obscures the construction.

   Either way, it doesn't make it easy to show a rule is valid,
   and it doesn't contribute to compositionality.
  *)

(* Really, a rule is valid if derived F X is sound *)
Definition derived_valid_0 (F : RRel -> RRel) :=
  forall X,
   subrel X (stepF (derived F X)) ->
   sound (derived F X).
(* With that definition, we can sum up the above lemmas as saying
   that derived_valid implies derived_valid_0 *)
Lemma obv1 F : validity_definition F -> derived_valid_0 F.
unfold derived_valid_0; intros; apply stable_sound; auto.
Qed.

Goal forall F, mono F -> derived_valid_0 F -> subrel (F reaches) reaches.
unfold mono, derived_valid_0, sound.
intros F F_mono F_valid.
eapply subrel_trans with (derived F reaches).
unfold subrel;intros. apply drule. 
revert x P H. apply F_mono. unfold subrel;eauto using dleaf.
apply F_valid.
clear;destruct 1;eauto using stepF,dleaf.
Qed.

Lemma deri_pres_close : forall F, mono F ->
                                  subrel (F reaches) reaches ->
                                  subrel (derived F reaches) reaches.
intros F H.
induction 2.
assumption.
apply Done;assumption.
eapply Step;eauto.
apply H in H2.
apply H0.
apply H2.
assumption.
Qed.

(* F reaches <= reaches means the least fixed point of F
   is no more than reaches,
   but that doesn't tell us a whole lot about the
   least fixed point greater than X,
   unless there's a lot more to squeeze out of
  X <= Step[Derived[F,X]] than I think.
   ... 
   for example, could define
   F[X] = emptyset if X <= reaches,
        = all      otherwise
   then Step[all] <= Step[Derived[F,X]],
   but F still meets the monotonicity and closedness
   conditions.,
   so it's not derived_valid_0.
 *)

Goal forall F, mono F ->
               subrel (F (derived F reaches)) reaches ->
               derived_valid_0 F.
unfold mono, derived_valid_0, sound.
intros F F_mono dF_closed X X_proof.
assert (subrel X reaches).
Abort.

(* So, what can we conclude just from derived_valid_0? *)
(* One conclusion, just from focusing on the drule' case in soundness *)
Lemma interesting F : derived_valid_0 F ->
  (forall X : RRel,
      subrel X (stepF (derived F X)) ->
      forall Q : RRel, subrel Q (derived F X) -> subrel (F Q) reaches).
Proof.
unfold derived_valid_0. unfold sound.
intro Hvalid0.
intros X HRel Q Qsub.
unfold subrel.
intros x P HF.
apply (Hvalid0 X HRel).
refine (drule' _ _ Qsub HF).
Qed.
End OverlySemanticNonsense.

(* Now we show that various rules satisfy the soundness conditions *)

(* Here's a generic proof tactic for derived_valid_m rule_type which
   assume a value of rule_type Q x P contains only one instance Q x S
   for any S. It splits it, tries to automtically finish from (S x) in
   the done case, and in the step case it takes the same step,
   assumes the remaining (derived F X) starts by drule,
   and hopes eauto finishes
 *)
Ltac simple_derived_rule :=
match goal with [|- derived_valid_m ?rule_type ] =>
destruct 1;match goal with
  [H : stepF _ ?x _ |- stepF _ ?x _] =>
  let Hstep := fresh "Hstep" in
  destruct H as [|? Hstep];
    [auto using DoneF
    |apply (StepF _ _ Hstep);clear x Hstep;apply drule]
end;eauto using rule_type, deri_step
end.

(* Transitivity using the generic derived rule mechanism *)
Inductive trans_rule (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dtrans : forall (Q : cfg -> Prop), X x Q ->
             (forall y, Q y -> X y P) -> trans_rule X x P.

Lemma trans_mono : mono trans_rule.
firstorder.
Qed.
Hint Resolve trans_mono : subrel.

Lemma trans_valid : derived_valid_m trans_rule.
simple_derived_rule.
Qed.

(* Definition trans_rule_sound := deri_sound trans_valid. *)

Inductive weak_rule (X : RRel) (x : cfg) (P : cfg -> Prop) : Prop :=
  | dweak : forall (Q : cfg -> Prop), (forall a, Q a -> P a) -> X x Q -> weak_rule X x P.

Lemma weak_mono : mono weak_rule.
firstorder.
Qed.

Lemma weak_valid : derived_valid_m weak_rule.
simple_derived_rule.
Qed.

(* A more semantical derived rule:
   if f is a simulation, we can project any
   true rule through it
  *)
Definition simul (f : cfg -> cfg) : Prop :=
  forall x y, step x y -> step (f x) (f y).

Definition img (f : cfg -> cfg) (P : cfg -> Prop) : cfg -> Prop :=
  fun y => exists x, y = f x /\ P x.

Lemma simul_sound f (Hf : simul f) :
  forall (x : cfg) (P : cfg -> Prop),
  reaches x P -> reaches (f x) (img f P).
cofix.
destruct 1.
apply Done. exists x. clear simul_sound; intuition.
apply Step with (f y).  clear simul_sound. auto.
apply simul_sound. assumption.
Qed.

Inductive automorph (f : cfg -> cfg) (X : RRel) : RRel :=
  | dsubst : forall x P, X x P -> automorph f X (f x) (img f P).

Lemma automorph_mono : forall f, mono (automorph f).
intro f. unfold mono. intros.
unfold subrel; intros.
destruct H0.
constructor. auto.
Qed.

Lemma automorph_valid : forall f, simul f ->
  derived_valid_m (automorph f).
intros.
unfold derived_valid_m, subrel.
intros X x P.
destruct 1.
destruct H0.
apply DoneF.
unfold img. exists x;intuition.
apply StepF with (f y).
auto.
apply drule. constructor. assumption.
Qed.

(* The most semantical derived rule ever *)
Definition ground_truth (X : RRel) : RRel := reaches.
Lemma gt_mono : mono ground_truth. firstorder. Qed.

Lemma gt_valid : derived_valid_m ground_truth.
unfold derived_valid_m, subrel.
intros.
destruct H.
apply DoneF. assumption.
apply StepF with y. assumption.
apply drule. assumption.
Qed.

(* Now let's consider rule compositionality *)

(* TODO
   Here's some new idea about composing rules even with the
   hypothesis about a proof of X.

   Need to check it's actually compositional.

   Probably need to say more about G
   if this is going to have any hope of being equivalent
   to the generic defition.
  *)
Definition compos_derived_valid (F : RRel -> RRel) : Prop :=
  forall X G, (forall Y, subrel (F Y) (G Y)) ->
     subrel X (stepF (derived G X)) ->
    subrel (F (stepF (derived G X))) (stepF (derived G X)).

(* To directly enable compositionaly, take derived_valid without
   the hypothesis on X, and generialize the rules allowed in
   the right hand sides to be any G pointwise greater than F.

   We'll prove further rules showing this equivalent to
   other things.
 *)
Definition derived_valid' (F : RRel -> RRel) : Prop :=
  forall (X Q : RRel) (G : RRel -> RRel)
    (HQ : subrel Q (stepF (derived G X)))
    (HG : forall X, subrel (F X) (G X)),
    subrel (F Q) (stepF (derived G X)).

(* Show this condition is preserved by monotonizing F,
   so we might as well assume F mono.
 *)
Lemma comp_valid1_wlog_mono (F : RRel -> RRel) :
  derived_valid' F <-> derived_valid' (monotonize F).
split.
destruct 4;by_subrel;eauto using monotonize_includes with subrel.

unfold derived_valid'.
intros Hvalid X Q G HQ HG.
specialize (Hvalid X Q (monotonize G)).
eapply subrel_trans;[apply monotonize_includes|].
eapply subrel_trans;[apply Hvalid|];clear Hvalid.
apply (subrel_trans HQ). apply stepF_mono;unfold subrel;apply derived_wlog_mono.
apply monotonize_pointwise;assumption.
apply stepF_mono;unfold subrel;apply derived_wlog_mono.
Qed.

(* For a monotone F, might as well pre-apply HQ *)
Definition derived_valid'' (F : RRel -> RRel) : Prop :=
  forall (X : RRel) (G : RRel -> RRel)
    (HG : forall X, subrel (F X) (G X)),
    subrel (F (stepF (derived G X))) (stepF (derived G X)).

(* 2 follows from 1 always *)
Lemma comp_valid2_from_1 : forall F, derived_valid' F -> derived_valid'' F.
Proof.
unfold derived_valid', derived_valid'',subrel;firstorder.
Qed.
(* 1 follows from 2 for monotone F *)
Lemma comp_valid1_from_2_when_mono : forall F (F_mono : mono F),
  derived_valid'' F -> derived_valid' F.
Proof.
unfold derived_valid'', derived_valid';eauto with subrel.
Qed.

(* Because we know nothing about G, and the first constructor of
   derived G X could be a drule, we might as well replace derived G X
   with an opaque set on the left. On the right, we just need to
   know we can apply F.
   So, this should be equivalent, but perhaps we won't
   be able to prove that.
  *)
Definition derived_valid''' (F : RRel -> RRel) : Prop :=
  forall (X : RRel), subrel (F (stepF X)) (stepF (derived F X)).

(* It implies 2, even without assuming monotonicity *)
Lemma comp_valid2_from_3 : forall F,
   derived_valid''' F -> derived_valid'' F.
unfold derived_valid''', derived_valid''.
eauto using deri_lift,deri_join_subrel with subrel.
Qed.

(* To go the other way, we have an arbitrary X,
   and need monotonicity to make use of the fact that
   any X is included in derived F X
 *)
Lemma comp_valid3_from_2_when_mono : forall F,
   mono F -> derived_valid'' F -> derived_valid''' F.
unfold derived_valid'', derived_valid'''.
intros. pose proof (dleaf_subrel F X); eauto with subrel.
Qed.

(* This is also very close to derived_valid_m *)
Lemma valid_m_from_3 : forall F,
  derived_valid''' F -> derived_valid_m F.
unfold derived_valid_m, derived_valid'''.
eauto using deri_join_subrel with subrel.
Qed.
Lemma comp_valid3_from_m_when_mono : forall F, mono F ->
  derived_valid_m F -> derived_valid''' F.
unfold derived_valid_m, derived_valid'''.
eauto using dleaf_subrel with subrel.
Qed.

Lemma derived'_from_m : forall F, mono F -> derived_valid_m F -> derived_valid' F.
intros;apply comp_valid1_from_2_when_mono;
[|apply comp_valid2_from_3;apply comp_valid3_from_m_when_mono];assumption.
Qed.

(* That's enough about equivalence of conditions.
   Let's show that some of these guys are actually compositional! *)

(* Combining rules *)
Definition union_rrel (R1 R2 : RRel) : RRel :=
  fun x P => R1 x P \/ R2 x P.
Lemma union_rrel_l (R1 R2: RRel) : subrel R1 (union_rrel R1 R2).
firstorder.
Qed.
Lemma union_rrel_r (R1 R2: RRel) : subrel R2 (union_rrel R1 R2).
firstorder.
Qed.

Hint Resolve stepF_mono union_rrel_l union_rrel_r : subrel.

Lemma union_split (P1 P2 Q : RRel) :
  subrel P1 Q -> subrel P2 Q -> subrel (union_rrel P1 P2) Q.
Proof.
firstorder.
Qed.
Hint Resolve union_split : subrel.

Inductive union_rules (F G : RRel -> RRel) (X : RRel) : RRel :=
  | d_union_left : forall x P, F X x P -> union_rules F G X x P
  | d_union_right : forall x P, G X x P -> union_rules F G X x P
  .

Lemma union_mono F G :
  mono F -> mono G -> mono (union_rules F G).
Proof. unfold mono, subrel.
destruct 4;[apply d_union_left|apply d_union_right];firstorder.
Qed.

(* Condition 3 is compositional, even without extra monotonicity assumptions *)
Lemma union_rules_valid''' F G :
  derived_valid''' F -> derived_valid''' G ->
  derived_valid''' (union_rules F G).
intros Fvalid Gvalid.
unfold derived_valid'''. intros X.
unfold subrel. intros x P.
destruct 1;[apply Fvalid in H|apply Gvalid in H];revert x P H;
apply stepF_mono;apply deri_lift;clear;unfold subrel;auto using union_rules.
Qed.

(* An example linking lemma *)
Lemma link2 (F : RRel -> RRel) (F_mono : mono F) (P1 Q1 P2 Q2 : RRel) :
            (subrel P1 (stepF (derived F Q1))) ->
            (subrel P2 (stepF (derived F Q2))) ->
            (subrel Q1 (union_rrel P1 P2)) ->
            (subrel Q2 (union_rrel P1 P2)) ->
            derived_stable F (union_rrel P1 P2).
unfold derived_stable;intros.
apply union_split;eauto with subrel.
Qed.
End Cotrans.