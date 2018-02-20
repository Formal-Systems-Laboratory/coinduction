
Require Import list_examples.

Require Import ZArith.
Require Import List.

(*
int sum_iterative(struct listNode* x)
//@ rule <k> $ => return sum(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  int s;
  
  s = 0;
  /*@ inv <heap>... lseg(old(x), x)(?A1), list(x)(?A2) ...</heap>
          /\ A = ?A1 @ ?A2 /\ s = sum(?A1) */
  while (x != NULL) {
    s += x->val;
    x = x->next;
  }

  return s;
}
*)

Definition sum_loop :=
  (SWhile (BNot (BEq (EVar "x") (ECon 0%Z)))
         (Seq (SAssign "s" (EPlus (EVar "s") (EProject (ELoad (EVar "x")) "val")))
              (SAssign "x" (EProject (ELoad (EVar "x")) "next")))).

Definition sum_code :=
 (Seq (SAssign "s" (ECon 0%Z))
 (Seq sum_loop
      (SReturn (EVar "s")))).

Inductive sum_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  sum_claim :
    forall c, kcell c = kra (KStmt sum_code) kdot ->
    forall xv sv, store c ~= "x" s|-> KInt xv :* "s" s|-> KInt sv ->
    forall l P, heap c |= rep_list l xv :* P->
      sum_spec c (returning c (sum l))
 |loop_claim :
    forall c, kcell c = kra (KStmt sum_loop) (kra (KStmt (SReturn (EVar "s"))) kdot) ->
    forall xv sv, store c ~= "x" s|-> KInt xv :* "s" s|-> KInt sv ->
    forall l P, heap c |= rep_list l xv :* P ->
      sum_spec c (returning c (sv + sum l)).

Lemma sum_proof : sound kstep sum_spec.
Proof.
list_solver.
Qed.