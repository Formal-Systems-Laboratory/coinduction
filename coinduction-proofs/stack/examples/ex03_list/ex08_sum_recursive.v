Require Import list_examples.

Definition sum_code :=
  Dup 0::If (Dup 0::Load::Swap::Plus1++Load
           ::Call "sum"::Binop Zplus::nil) nil
  ::Ret::nil.

Definition sum := fold_right Zplus 0.
Inductive sum_spec : Spec cfg :=
  sum_claim : forall H l, fun_claim sum_spec
  "sum" sum_code
    1 (fun p => asP H (rep_list l p))
    1 (fun n => constraint (n = sum l) :* litP H).

Lemma sum_proof : sound stack_step sum_spec.
Proof. list_solver. Qed.
