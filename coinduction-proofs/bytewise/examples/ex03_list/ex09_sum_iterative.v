
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

Open Scope Z.

Definition sum_loop :=
  (SWhile ("x" <> 0)
         (Seq ("s" <- "s" + ELoad "x")
              ("x" <- ELoad ("x" + 1))))%code.

Definition sum_code :=
 (Seq ("s" <- 0)
 (Seq sum_loop
      (SReturn "s")))%code.

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
