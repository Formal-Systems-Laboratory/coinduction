Require Import list_examples.

Definition length_loop :=
  SWhile (BNot (BEq (EVar "x") (ECon 0)))
              (Seq (SAssign "l" (EPlus (EVar "l") (ECon 1)))
                   (SAssign "x" (EProject (ELoad (EVar "x")) "next"))).
Definition length_code :=
  Seq (SAssign "l" (ECon 0%Z))
 (Seq length_loop
     (SReturn (EVar "l"))).

Inductive length_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  length_claim :
    forall c,
      kcell c = kra (KStmt length_code) kdot ->
    forall xv lv,
      store c ~= ("x" s|-> KInt xv :* "l" s|-> KInt lv) ->
    forall l P,
      heap c |= rep_list l xv :* P ->
      length_spec c (returning c (zlength l))
 |loop_claim :
    forall c,
      kcell c = kra (KStmt length_loop) (kra (KStmt (SReturn (EVar "l"))) kdot) ->
    forall xv lv,
      store c ~= ("x" s|-> KInt xv :* "l" s|-> KInt lv) ->
    forall l P,
      heap c |= rep_list l xv :* P ->
      length_spec c (returning c (zlength l + lv)).

Lemma length_proof : sound kstep length_spec.
Proof.
list_solver.
Qed.