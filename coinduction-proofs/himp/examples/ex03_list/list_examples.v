Require Export himp_steps.
Require Export himp_syntax_sugar.

Require Export himp_tactics.

Require Export patterns.
Require Export pattern_tactics.

Require Export list_predicates.
Require Export list_tactics.

(* Operations we'll implement for concrete linked lists *)
Fixpoint zlength {A} (l : list A) :=
  match l with
    | nil => 0
    | _ :: l' => 1 + zlength l'
  end.
Definition sum : list Z -> Z := fold_right Zplus 0.

Global Open Scope Z_scope.
Global Open Scope pattern.
