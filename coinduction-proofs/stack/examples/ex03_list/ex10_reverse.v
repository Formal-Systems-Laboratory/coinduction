Require Import list_examples.

Definition reverse_code :=
  Push 0::While (Over::nil)
    (Dup 1::Plus1++Load::Swap::Dup 2::Plus1++Store::Swap::nil)
  ::Swap::Drop::Ret::nil. 

Inductive reverse_spec : cfg -> (cfg -> Prop) -> Prop :=
  reverse_claim : forall l, fun_claim reverse_spec
  "reverse" reverse_code
    1 (rep_list l) 1 (rep_list (rev l))
 |loop_claim : forall lx lp, loop_claim reverse_spec
  0 reverse_code
    2 (fun p x => rep_list lx x :* rep_list lp p)
    1 (rep_list (rev_append lx lp)).

Lemma reverse_proof : sound stack_step reverse_spec.
Proof. list_solver;
rewrite <- rev_alt in * |-;
list_run. Qed.
