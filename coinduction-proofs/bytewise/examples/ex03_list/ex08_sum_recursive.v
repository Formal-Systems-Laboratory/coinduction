Require Import list_examples.

Require Import ZArith.
Require Import List.

(*

int sum_recursive(struct listNode* x)
//@ rule <k> $ => return sum(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  if (x == NULL)
    return 0;

  return x->val + sum_recursive(x->next);
}
*)

Open Scope Z.
Definition sum_code :=
 (SIf ("x" = 0)
      (SReturn 0)
      (SReturn (EPlus (ELoad "x") (ECall "sum_recursive" [ELoad ("x" + 1)]))))%code.
Definition sum_fun :=
  FunDef "sum_recursive" ["x"] sum_code.
Inductive sum_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  sum_claim :
    forall c, kcell c = kra (KStmt sum_code) kdot ->
    forall xv, store c ~= "x" s|-> KInt xv ->
    forall f', functions c ~=  "sum_recursive" s|-> sum_fun :* f' ->
    forall l P, heap c |= rep_list l xv :* P ->
      sum_spec c (returning c (sum l)).

Lemma sum_proof : sound kstep sum_spec.
Proof.
list_solver.
Qed.
