Require Import list_examples.

Definition inf_code :=
  Push 1::While (Dup 0::nil)
    (Plus1)
    ::Ret::nil.

Definition inf_cfg stk rstk heap funs mark n :=
  {|
    code := While (Dup 0 :: nil) Plus1 :: Ret :: nil;
    stack := n :: stk;
    rstack := rstk;
    heap := heap;
    functions := funs;
    alloc_next := mark
  |}.

Inductive inf_spec : Spec cfg :=
  inf_claim : forall H l, fun_claim inf_spec
  "inf" inf_code
    1 (fun p => asP H (rep_list l p))
    1 (fun n => constraint False)
  |inf_loop_claim : forall stk rstk heap funs mark n,
      n > 0 -> inf_spec (inf_cfg stk rstk heap funs mark n) (fun c => False).

Lemma inf_proof : sound stack_step inf_spec.
Proof. list_solver; contradiction. Qed.
