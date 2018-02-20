Require Import list_examples.

Definition sum_code :=
  Push 0::Swap::While (Dup 0::nil)
    (Swap::Over::Load::Binop Zplus::Swap::Plus1++Load::nil)
  ::Drop::Ret::nil.

Definition sum := fold_right Zplus 0.
Inductive sum_spec : Spec cfg :=
  sum_claim : forall H l, fun_claim sum_spec
  "sum" sum_code
    1 (fun p => asP H (rep_list l p))
    1 (fun n => constraint (n = sum l) :* litP H)
 |loop_claim : forall H n l, loop_claim sum_spec
  0 sum_code
    2 (fun p k => constraint (k = n) :* asP H (rep_list l p))
    1 (fun k => constraint (k = n + sum l) :* litP H).

Lemma sum_proof : sound stack_step sum_spec.
Proof. list_solver. Qed.