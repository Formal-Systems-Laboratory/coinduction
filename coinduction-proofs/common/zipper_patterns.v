Require Import maps.
Require Import patterns.

(* This module defines a zipper over patterns to
   allow moving terms of interest to the front by reflection
   rather than by assembling large proof terms.
 *)

Inductive pat_context {Key Elt : Type} : Type :=
    Top
  | LeftOf (p : MapPattern Key Elt) (rest : pat_context)
  | RightOf (p : MapPattern Key Elt) (rest : pat_context)
  .

Fixpoint close {Key Elt} pat ctx : MapPattern Key Elt :=
  match ctx with
    | Top => pat
    | LeftOf p ctx' => close (pat :* p)%pattern ctx'
    | RightOf p ctx' => close (p :* pat)%pattern ctx'
  end.

Fixpoint close_empty {Key Elt} ctx : MapPattern Key Elt :=
  match ctx with
    | Top => mapEmpty%pattern
    | LeftOf p ctx' => close p ctx'
    | RightOf p ctx' => close p ctx'
  end.

Lemma lifting : forall {Key Elt} ctx (p : MapPattern Key Elt),
  PatEquiv (close p ctx) (p :* close_empty ctx).
induction ctx;simpl;intros.
rewrite patEquivUnit. reflexivity.
rewrite 2 IHctx, patEquivAssoc; reflexivity.
rewrite 2 IHctx, patEquivAssoc, patEquivCommAssoc; reflexivity.
Qed.

(* Search through a MapPattern pat for
   the given term target, adding the context
   passed through onto context ctx,
   and ending on success by calling the
   continuation k with the pattern found and
   the constructed context.
 *)
Ltac quote_zipper target pat ctx k :=
  first [unify target pat;k pat ctx
   |  match pat with
      | (?l :* ?r)%pattern =>
          first [let ctx' := constr:(LeftOf r ctx) in
                 quote_zipper target l ctx' k
                |let ctx' := constr:(RightOf l ctx) in
                 quote_zipper target r ctx' k
                ]  
      | (asP ?h ?P)%pattern =>
          unify target P;k pat ctx
  end].

(*
Lemma lift_constraint : forall {Key Elt} (h : Map Key Elt) ctx P,
  h |= close (constraint P) ctx <-> (P /\ h |= close_empty ctx).
intros.
rewrite lifting.
(* now extract the P *)
Transparent satisfies.
simpl.
Opaque satisfies.
firstorder.
revert H0;apply pats_good. equate_maps.
eexists;eexists. firstorder (eauto || equate_maps).
Qed.
 *)