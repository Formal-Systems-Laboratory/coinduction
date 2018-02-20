Require Export "fun_semantics".

Set Implicit Arguments.

(** The undefined examples will reach a stuck configuration.
    Define the predicate for a configuration being stuck *)
Definition stuck (c : kcfg) : Prop :=
  forall c', ~ kstep c c'.

(** Here's a simple claim that a particular starting configuration gets stuck.
    If we don't need circularities, we can use this putting quantification
    over variables in the initial state outside.
 *)
Inductive gets_stuck (c : kcfg) : kcfg -> (kcfg -> Prop) -> Prop :=
  stuck_claim : gets_stuck c c stuck.

(** Register a tactic for proving a configuration stuck *)
Hint Extern 1 (stuck _) =>
  unfold stuck;intro;inversion 1;
  simpl in * |- *;
  try match goal with
  [H : Some _ = Some _ |- _] =>
    inversion H;subst;clear H
  end;
  discriminate
  : done_hints.

Ltac undefined_solver := generic_solver fail step_solver done_solver fail.