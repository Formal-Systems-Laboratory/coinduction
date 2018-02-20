Require Import list_examples.

Require Import ZArith.
Require Import List.

Open Scope Z.

Definition tail_code :=
  SReturn (ELoad ("x" + 1))%code.

Lemma tail_spec : forall c, kcell c = kra (KStmt tail_code) kdot ->
    forall xv,
      store c ~= ("x" s|-> KInt xv) ->
    forall hd tl m (p_tl :Z),
      heap c |= xv h|-> hd :* (xv+1) h|-> p_tl :* rep_list tl p_tl :* litP m
     -> sound kstep (returns c p_tl).
Proof.
list_solver.
Qed.
