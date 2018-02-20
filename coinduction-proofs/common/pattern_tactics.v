Require Import maps.
Require Import patterns.

Set Implicit Arguments.

Lemma emptyP_expose : forall {Key Val} (h : Map Key Val),
  h |= mapEmpty <-> h ~= mapEmpty.
reflexivity.
Qed.
Lemma itemP_expose : forall {Key Val} (h : Map Key Val) k v,
  h |= itemP k v <-> h ~= k |-> v.
reflexivity.
Qed.
Lemma litP_expose : forall {Key Val} (h : Map Key Val) h',
  h |= litP h' <-> h ~= h'.
reflexivity.
Qed.
Lemma constraint_expose : forall {Key Val} (h : Map Key Val) P,
  h |= constraint P <-> (P /\ h ~= mapEmpty).
reflexivity.
Qed.

(* Try to eliminate a hypothesis H : h ~= _
   by rewriting with it everywhere, unless
   it appears in the conclusion
   (in the conclusion it's likely to be
    stuck under something we don't know
    how to rewrite under, and in that condition
    a rewrite can waste a second or two figuring
    out it is going to fail)
 *)
Ltac try_subst_map h H :=
  match goal with
  | [|- context C [h]] => idtac
  | _ => rewrite ?H in * |- *; clear h H
  end.

(* Find a hypothesis where a pattern has some explicit
   map structure, and break it down into a map
   equality and maybe some simpler patterns *)
Ltac simplify_pat_hyp := match goal with
| [H : ?h |= exP _ |- _ ] => destruct H
| [H : ?h |= asP _ _ |- _] =>
    let Heq := fresh "Heq" in
    destruct H as [Heq];try_subst_map h Heq
| [H : ?h |= emptyP |- _] =>
  rewrite emptyP_expose in H;try_subst_map h H
| [H : ?h |= itemP _ _ |- _] =>
  rewrite itemP_expose in H;try_subst_map h H
| [H : ?h |= litP _ |- _] =>
  rewrite litP_expose in H;try_subst_map h H
| [H : ?h |= constraint _ |- _] =>
  let Heq := fresh "Heq" in
  destruct H as [? Heq];try_subst_map h Heq
| [H : ?h |= _ :* _ |- _] =>
  let Heq := fresh "Heq" in
  destruct H as (? & ? & ? & ? & Heq);try_subst_map h Heq
end.

(* Simplify all pattern hypotheses, then clean
   up any empty maps and mis-associated terms that
   might be left in map equalities *)
Ltac simplify_pat_hyps := repeat simplify_pat_hyp;
  rewrite ?@equivAssoc, ?@equivUnitL, ?@equivUnit  in * |- .
