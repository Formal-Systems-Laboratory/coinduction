Require Import list_examples.

Definition dealloc_code :=
  While (Dup 0::nil) (Dup 0::Plus1++Swap::Dealloc
                    ::Dup 0::Load::Swap::Dealloc::nil)
  ::Drop::Ret::nil.

Inductive dealloc_spec : Spec cfg :=
  dealloc_claim : forall l, fun_claim dealloc_spec
    "dealloc" dealloc_code 1 (rep_list l) 0 emptyP
 |loop_claim : forall l, loop_claim dealloc_spec
            0 dealloc_code 1 (rep_list l) 0 emptyP.

Lemma dealloc_proof : sound stack_step dealloc_spec.
Proof. list_solver. Qed.