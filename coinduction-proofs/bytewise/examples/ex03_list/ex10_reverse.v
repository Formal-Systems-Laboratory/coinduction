Require Import list_examples.

Require Import ZArith.
Require Import List.

(*
struct listNode* reverse(struct listNode *x)
/*@ rule <k> $ => return ?p; ...</k>
         <heap>... list(x)(A) => list(?p)(rev(A)) ...</heap> */
{
  struct listNode *p;

  p = NULL;
  //@ inv <heap>... list(p)(?B), list(x)(?C) ...</heap> /\ A = rev(?B) @ ?C
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}
*)

Open Scope Z.

Definition reverse_loop :=
  SWhile ("x" <> 0)
    {{"y"   <- ELoad ("x" + 1)
     ;"x"+1<<-"p"
     ;"p"  <- "x"
     ;"x"  <- "y"
     }}.

Definition reverse_code :=
  {{"p" <- 0
   ;reverse_loop
   ;SReturn "p"
   }}%code.

Inductive reverse_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  reverse_claim :
    forall c, kcell c = kra (KStmt reverse_code) kdot ->
    forall xv yv pv, store c ~= "x" s|-> KInt xv :* "y" s|-> KInt yv :* "p" s|-> KInt pv ->
    forall l m, heap c |= rep_list l xv :* litP m ->
      reverse_spec c (returns_list c (rev l) m)
 |loop_claim :
    forall c, kcell c = kra (KStmt reverse_loop) (kra {{SReturn "p"}}%code kdot) ->
    forall xv yv pv, store c ~= "x" s|-> KInt xv :* "y" s|-> KInt yv :* "p" s|-> KInt pv ->
    forall lx lp m, heap c |= rep_list lx xv :* rep_list lp pv :* litP m ->
      reverse_spec c (returns_list c (rev_append lx lp) m).

Lemma reverse_proof : sound kstep reverse_spec.
Proof.
list_solver.
rewrite <- rev_alt in * |- . (* Needs a touch of help re-expressing rev to finish *)
list_run.
Qed.