Require Import list_examples.

Require Import ZArith.
Require Import List.

Open Scope Z.

Definition swap_code :=
 {{"p" <- "x"
  ;"x" <- ELoad ("x"+1)
  ;"p"+1 <<- ELoad ("x"+1)
  ;"x"+1 <<- "p"
  ;SReturn "x"
  }}%code.

Inductive swap_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  swap_claim :
  forall c, kcell c = kra (KStmt swap_code) kdot ->
    forall xv pv,
      store c ~= ("x" s|-> KInt xv :* "p" s|-> KInt pv) ->
    forall v1 v2 l m,
      heap c |= rep_list (v1 :: v2 :: l) xv :* litP m ->
    swap_spec c (fun c' =>
       exists v',
         returning_heap_pat c
                            (rep_list (v2 :: v1 :: l) v' :* litP m)
                            v'
                            c').

Lemma swap_proof : sound kstep swap_spec.
Proof.
list_solver.
Qed.