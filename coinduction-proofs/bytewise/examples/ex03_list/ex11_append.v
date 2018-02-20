Require Import list_examples.

Require Import ZArith.
Require Import List.

(*

struct listNode* append(struct listNode *x, struct listNode *y)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A), list(y)(B) => list(?x)(A @ B) ...</heap> */
{
  struct listNode *p;
  if (x == NULL)
    return y;

  p = x;
  /*@ inv <heap>... lseg(x, p)(?A1), list(p)(?A2) ...</heap> 
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) */
  while (p->next != NULL)
    p = p->next;
  p->next = y;

  return x;
}

//@ var A, B : Seq
*)

Open Scope Z.

Definition append_loop :=
  (SWhile (ELoad ("p" + 1) <> 0)
      ("p" <- ELoad ("p"+1)))%code.
Definition append_tail :=
 {{"p"+1 <<- "y"
  ;SReturn "x"
  }}%code.
Definition append_code :=
  SIf ("x"=0)
    (SReturn (EVar "y"))
    (Seq ("p" <- "x")
    (Seq append_loop
         append_tail))%code.

Inductive append_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  append_claim : forall c,
    kcell c = kra (KStmt append_code) kdot ->
    forall xv yv pv, store c ~= "x" s|-> KInt xv :* "y" s|-> KInt yv :* "p" s|-> KInt pv ->
    forall lx ly m, heap c |= rep_list lx xv :* rep_list ly yv :* litP m ->
      append_spec c (returns_list c (lx ++ ly) m)
 |loop_claim : forall c,
    kcell c = kra (KStmt append_loop) (kra (KStmt append_tail) kdot) ->
    forall xv yv pv, store c ~= "x" s|-> KInt xv :* "y" s|-> KInt yv :* "p" s|-> KInt pv ->
    pv <> 0%Z ->
    forall lx lp ly m, heap c |= rep_seg lx pv xv :* rep_list lp pv :* rep_list ly yv :* litP m ->
      append_spec c (returns_list c (lx ++ lp ++ ly) m).

Lemma append_proof : sound kstep append_spec.
list_solver.
rewrite app_ass in * |-.
list_run.
Qed.
