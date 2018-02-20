Require Import list_examples.

Require Import ZArith.
Require Import List.

Definition head_code :=
  SReturn (ELoad (EVar "x")).

Lemma head_spec : forall c, kcell c = kra (KStmt head_code) kdot ->
    forall xv,
      store c ~= ("x" s|-> KInt xv) ->
    forall hd tl m,
      heap c |= rep_list (hd :: tl) xv :* litP m
     -> sound kstep (returns c hd).
Proof.
list_solver.
Qed.