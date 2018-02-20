(* Require Import domains. *)
Require Import maps.
Require Import Setoid.

Set Implicit Arguments.

(* Define a language of map patterns.
   A map pattern is basically just a pattern over maps,
   but hidden under a definition so it doesn't reduce
   too eagerly, and with standard definitions of
   patterns for items, union, literal, and empty maps.
   Particular interesting are existential quantifers.

   Specifications are expected to define their own
   predicates, which should be possible in terms
   of these primitives.
 *)

Section Pattern.
Variables (Key Elt : Type).

(* A pattern is a predicate on maps which respects map equivalence.
   The predicate and proof are packaged together to be sure we
   can't accidentally use ill-defined predicates as patterns. *)
Definition MapPattern' := Map Key Elt -> Prop.
Definition GoodPat (P : MapPattern') : Prop :=
  forall h1 h2, h1 ~= h2 -> (P h1 <-> P h2).
Definition MapPattern : Type :=
  { P : Map Key Elt -> Prop | GoodPat P }.

(**
A map satisfies a predicate if the predicate holds on a map.
These definitions also seem to mostly prevent simpl from
unfolding applications of "satsifies".
(we can explicitly "unfold satisfies" for proving lemmas)
 *)   
Definition satisfies (c : Map Key Elt) (P : MapPattern) : Prop := proj1_sig P c.

(** Now come the pasic patterns *)

(** An empty map *)
Definition emptyP : MapPattern.
refine (exist _ (fun h => h ~= mapEmpty) _).
abstract (unfold GoodPat;simpl;split;intuition;equate_maps).
Defined.

(** A single item *)
Definition itemP (k : Key) (v : Elt) : MapPattern.
refine (exist _ (fun h => h ~= k |-> v) _).
abstract (split;intros;equate_maps).
Defined.

(** Joining two patterns *)
Definition joinP (mp1 mp2 : MapPattern) : MapPattern.
refine (exist _ (fun h => exists h1, exists h2,
  satisfies h1 mp1 /\ satisfies h2 mp2 /\ h ~= h1 :* h2) _).
abstract (split;destruct 1 as [? []];eexists;eexists;intuition eauto;equate_maps).
Defined.

(** Making a pattern from an entire concrete map *)
Definition litP (h : Map Key Elt) : MapPattern.
refine (exist _ (fun m => m ~= h) _).
abstract (split;intros;equate_maps).
Defined.

(**
Embedding a pure predicate as a map pattern.
Satisfiable only if the predicate is true, and then matches an empty map.
*)
Definition constraint (P : Prop) : MapPattern.
refine (exist _ (fun h => P /\ h ~= mapEmpty) _).
  abstract(split;intuition;equate_maps).
Defined.

(** Now for two slightly more involved things *)

(** Patterns can include existential qunantification.

This is necessary as parts of things like patterns for linked lists,
where we need to existentially quantify over the address of the
second node
*)
Definition exP {A : Type} (P : A -> MapPattern) : MapPattern.
refine (exist _ (fun h => exists (x : A), satisfies h (P x)) _).
abstract (unfold GoodPat,satisfies;split;destruct 1;
   destruct (proj2_sig (P x) _ _ H);eauto).
Defined.

(** The last pattern we define is more specialized.
It matches a specific map, but also records that the map
satisfies a pattern.

This is somewhat specialized.

It is intended to be used mostly with map variables where
all we know about them is that they satisfy some pattern.
If we want to prove pattern implications with a pattern
involving asP on the left, we can handle desired patterns
that either want the exact submap, or just care about the
property.
*)
Definition asP (h : Map Key Elt) (P : MapPattern) : MapPattern.
refine (exist _ (fun h' => h' ~= h /\ satisfies h P) _).
unfold GoodPat,satisfies;split;destruct 1;
   (split;[equate_maps|assumption]).
Defined.

End Pattern.

(** Next we define notations for writing patterns.

The same notations are used for the basic item/join/empty patterns
as for the map constructors.
They are put in a different notation scope, which is automatically
added in appropriate arguments of the pattern operators,
so there should be no confusion with maps.
 *)
Delimit Scope MapPattern with pattern.
Bind Scope MapPattern with MapPattern.

Notation "h |= p" := (satisfies h%Map p%pattern) (at level 80, no associativity).

Infix "|->" := itemP (at level 50, no associativity) : MapPattern.

Arguments joinP {Key Elt} (mp1 mp2)%pattern.
Notation "m1 :* m2" := (joinP m1%pattern m2%pattern) (at level 60, right associativity) : MapPattern.

(* Using a name as a notation shadows any ordinary identifier,
   so we need to redeclare mapEmpty for Map as a notation too *)
Arguments emptyP {Key Elt}.
Notation "'mapEmpty'" := mapEmpty : Map.
Notation "'mapEmpty'" := emptyP : MapPattern.

Arguments exP {Key Elt A} P%pattern.
Notation "'existP' x ',' e" :=
  ((exP (fun x =>e))%pattern)
  (at level 70) : MapPattern.
Notation "'existsP' x .. y ',' e" :=
  (exP (fun x => .. (exP (fun y => e)) ..)%pattern)
  (at level 70, x binder, y binder) : MapPattern.

Arguments constraint {Key Elt} P%type.

(**
The next step is to define pattern equivalence and implication,
and enable rewriting by these relations.
*)

(** First, declare PatEquiv as an equivalence relation *)
Definition PatEquiv {Key Elt} (A B : MapPattern Key Elt) :=
  forall h, h |= A <-> h |= B.

Lemma patEquivTrans : forall {Key Elt} (m1 m2 m3 : MapPattern Key Elt), PatEquiv m1 m2 -> PatEquiv m2 m3 -> PatEquiv m1 m3.
Proof. firstorder. Qed.

Lemma patEquivSym : forall {Key Elt} (m1 m2 : MapPattern Key Elt),
                      PatEquiv m1 m2 -> PatEquiv m2 m1.
Proof. firstorder. Qed.

Lemma patEquivRefl : forall {Key Elt} (m : MapPattern Key Elt),
                       PatEquiv m m.
Proof. firstorder. Qed.

Add Parametric Relation Key Elt : (MapPattern Key Elt) PatEquiv
  reflexivity proved by (@patEquivRefl Key Elt)
  symmetry proved by (@patEquivSym Key Elt)
  transitivity proved by (@patEquivTrans Key Elt)
  as pat_equiv_rel.

(** Additionally Show PatEquiv is associative and commutative, with unit emptyP *)

(* A little custom tactic for proving these lemmas about PatEquiv *)
Local Ltac pat_equiv_solver :=
split;(intros;repeat match goal with
| [H : _ |= (_ :* _)%pattern |-_] => destruct H as [? [? [? []]]]
| [H : _ |=  ?P |-_] => progress (simpl in H)
end;
repeat 
match goal with
  | [|- _ |= (_ :* _)%pattern] => eexists;eexists;repeat split
  | [H : _ |= ?P |- _ |= ?P] => eexact H
  | [|- _ ~= _] => equate_maps
  | [|- _ |= mapEmpty%pattern] => simpl
  | [H : _ |= ?P |- _ |= ?P] => revert H;apply (proj2_sig P)
  | [H  : PatEquiv ?A ?B |- _ |= ?A] => apply H
  | [H  : PatEquiv ?B ?A |- _ |= ?A] => apply H
  | _ => progress (instantiate;simpl)
end).

Lemma patEquivComm : forall {Key Elt} (m1 m2 : MapPattern Key Elt),
    PatEquiv (m1 :* m2) (m2 :* m1).
Proof. pat_equiv_solver. Qed.

Lemma patEquivAssoc : forall {Key Elt} (m1 m2 m3 : MapPattern Key Elt),
                        PatEquiv ((m1 :* m2) :* m3) (m1 :* (m2 :* m3)).

Proof. pat_equiv_solver. Qed.

Lemma patEquivUnit : forall {Key Elt} (m : MapPattern Key Elt),
                       PatEquiv (m :* mapEmpty) m.
Proof. pat_equiv_solver. Qed.

Lemma patEquivUnitL : forall {Key Elt} (m : MapPattern Key Elt),
                       PatEquiv (mapEmpty :* m) m.
Proof. pat_equiv_solver. Qed.

Lemma patEquivCommAssoc : forall {Key Elt} (m1 m2 m3 : MapPattern Key Elt),
                        PatEquiv (m1 :* m2 :* m3) (m2 :* m1 :* m3).
Proof. pat_equiv_solver. Qed.

(** Now declare appropriate morphisms to allow rewriting by PatEquiv
    equivalences in pattern arguments of operators we have defined so far *)

(** In particular, we can rewrite in the arguments of PatEquiv itself *)
Add Parametric Morphism Key Elt : (@PatEquiv Key Elt) with
  signature PatEquiv ==> PatEquiv ==> iff as pat_equiv_resp_equiv.
Proof. firstorder. Qed.

(** Register satisfies as a morphism from MapEquiv and PatEquiv
    to logical equivalence *)
Add Parametric Morphism Key Elt : (@satisfies Key Elt) with
  signature MapEquiv ==> PatEquiv ==> iff as satisfies_iff.
Proof. pat_equiv_solver. Qed.

Add Parametric Morphism Key Elt : (@asP Key Elt) with
  signature MapEquiv ==> PatEquiv ==> PatEquiv as asP_equiv_mor.
Proof. intros. unfold PatEquiv. simpl. intro.
  rewrite H. rewrite H0. reflexivity. Qed.

(** Register litP as a morphism from MapEquiv to PatEquiv *)
Add Parametric Morphism Key Elt : (@litP Key Elt) with
  signature MapEquiv ==> PatEquiv as pat_lit_mor.
Proof. pat_equiv_solver. Qed.

(** Register joinP as a congruence for PatEquiv *)
Add Parametric Morphism Key Elt : (@joinP Key Elt) with
  signature PatEquiv ==> PatEquiv ==> PatEquiv as pat_equiv_join_mor.
Proof. pat_equiv_solver. Qed.

(** Next, we make define pattern implication, and register it as
    a reflexive-transitive relation, which also enables some
    rewriting tactics *)
Definition PatImpl {Key Elt : Type} (A B : MapPattern Key Elt) : Prop :=
  forall h, h |= A -> h |= B.

Lemma patImplRefl : forall {Key Elt} (m : MapPattern Key Elt),
                       PatImpl m m.
Proof. firstorder. Qed.

Lemma patImplTrans : forall {Key Elt} (m1 m2 m3 : MapPattern Key Elt),
                       PatImpl m1 m2 -> PatImpl m2 m3 -> PatImpl m1 m3.
Proof. firstorder. Qed.

Add Parametric Relation Key Elt : (MapPattern Key Elt) PatImpl
  reflexivity proved by (@patImplRefl Key Elt)
  transitivity proved by (@patImplTrans Key Elt)
  as pat_impl_rel.

(** PatEquiv is a subrelation of PatImpl and inverse PatImpl. *)
Require Import Coq.Classes.Morphisms.
Instance map_pat_equiv_impl_subrelation : forall {Key Elt : Type},
  subrelation (@PatEquiv Key Elt) PatImpl | 2.
Proof. firstorder. Qed.

Instance map_pat_equiv_inverse_impl_subrelation : forall {Key Elt : Type},
  subrelation (@PatEquiv Key Elt) (inverse PatImpl) | 2.
Proof. firstorder. Qed.

(** We also define various morphisms respecting PatImpl *)

(** In particular, argument to PatImpl itself can be rewritten with PatImpl *)
Add Parametric Morphism Key Elt : (@PatImpl Key Elt) with
  signature PatImpl --> PatImpl ++> Basics.impl as pat_impl_resp_impl.
Proof. firstorder. Qed.
Add Parametric Morphism Key Elt : (@PatImpl Key Elt) with
  signature PatEquiv ==> PatEquiv ==> iff as pat_impl_resp_equiv.
Proof. firstorder. Qed.

Add Parametric Morphism Key Elt : (@joinP Key Elt) with
  signature PatImpl ==> PatImpl ==> PatImpl as patImplJoin.
Proof. firstorder. Qed.

Add Parametric Morphism Key Elt : (@satisfies Key Elt) with
  signature MapEquiv ==> PatImpl ==> Basics.impl as satisfies_impl.
Proof.
unfold PatImpl, Basics.impl, satisfies; firstorder;apply H0.
revert H H1;apply (proj2_sig x0).
Qed.

Add Parametric Morphism Key Elt : (@asP Key Elt) with
  signature MapEquiv ++> PatImpl ++> PatImpl as pat_impl_asP_mor.
Proof. intros. unfold PatImpl. firstorder. equate_maps.
  rewrite <- H, <- H0. assumption. Qed.

(*
Add Parametric Morphism Key Elt : (@asP Key Elt) with
  signature MapEquiv ==> PatEquiv ==> PatEquiv as pat_equiv_as_mor.
unfold PatEquiv;simpl;intuition;try equate_maps.
apply H0;eauto using pats_good.
symmetry in H.
apply H0;eauto using pats_good.
Qed.

*)

Lemma pats_good {Key Elt} (h1 h2 : Map Key Elt) P : h1 ~= h2 -> h1 |= P -> h2 |= P.
Proof. apply (proj2_sig P). Qed.

Lemma asP_forget_heap : forall Key Elt h (P : MapPattern Key Elt),
  PatImpl (asP h P) P.
Proof.
unfold PatImpl. firstorder.
symmetry in H. revert H H0. apply pats_good.
Qed.

Lemma asP_forget_pat : forall Key Elt h (P : MapPattern Key Elt),
  PatImpl (asP h P) (litP h).                       
unfold PatImpl;simpl;intuition.
Qed.

Lemma constraint_true_simpl : forall {Key Elt} (P : Prop),
  P -> PatEquiv (constraint P) (emptyP : MapPattern Key Elt).
Proof. firstorder. Qed.

(* Seems like this ought to be enough to support rewriting? *)
(*

(* Now, about extracting things *)
Lemma item_split_iff_pat : forall Key Elt (k : Key) (v : Elt)
  (h : Map Key Elt) (P : MapPattern Key Elt),
  h |= k |-> v :* P <-> exists m, h ~= k |-> v :* m /\ m |= P.
split;intros;simpl in * |- *;decompose record H;clear H;
repeat eexists;repeat split;(eassumption || equate_maps).
Qed.

Lemma item_split_manifest : forall Key Elt (k : Key) (v : Elt) (h : Map Key Elt)
  (P : MapPattern Key Elt),
  Basics.impl (h |= P) (k |-> v :* h |= k |-> v :* P).
intros.
simpl.
eexists;eexists;repeat split;eassumption || equate_maps.
Qed.

Lemma lit_split_iff : forall Key Elt (h m : Map Key Elt) P,
  h |= litP m :* P <-> (exists h', h ~= m :* h' /\ h' |= P).
split;intros;simpl in * |- *;decompose record H;clear H;
repeat eexists;repeat split;(eassumption || equate_maps).
Qed.

Lemma lit_split_manifest : forall Key Elt (m h : Map Key Elt)
  (P : MapPattern Key Elt),
  (h |= P) -> (m :* h |= litP m :* P).
intros.
simpl.
eexists;eexists;repeat split;eassumption || equate_maps.
Qed.

*)

Global Opaque satisfies.