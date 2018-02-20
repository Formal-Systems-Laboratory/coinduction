Require Import list_examples.

Require Import ZArith.
Require Import List.

(*
int length_recursive(struct listNode* x)
//@ rule <k> $ => return len(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  if (x == 0)
    return 0;

  return 1 + length_recursive(x->next);  
}


//@ var A : Seq
*)

Open Scope Z.

Definition length_code :=
 (SIf ("x" = 0)
      (SReturn 0)
      (SReturn (1 + ECall "length_recursive"
                      [ELoad (EVar "x" + 1)])))%code.

Inductive length_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  length_claim :
    forall c,
      kcell c = kra (KStmt length_code) kdot ->
    forall xv,
      store c ~= "x" s|-> KInt xv ->
    forall f',
      functions c ~=
        "length_recursive" s|-> FunDef "length_recursive" ["x"] length_code :* f' ->
    forall l P,
      heap c |= rep_list l xv :* P ->
      length_spec c (returning c (zlength l)).

Lemma length_proof : sound kstep length_spec.
Proof.
list_solver.
Qed.
