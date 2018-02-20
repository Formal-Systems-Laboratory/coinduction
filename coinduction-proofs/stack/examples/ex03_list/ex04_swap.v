Require Import list_examples.

Definition swap_code :=
  Dup 0::Load::Over::Plus1++Load::Dup 0::Load
  ::Roll 2::Store::Over::Store::Ret::nil.

Inductive swap_spec : Spec cfg :=
  swap_claim : forall x y t, fun_claim swap_spec
  "swap" swap_code
    1 (rep_seg (x::y::nil) t) 1 (rep_seg (y::x::nil) t).

Lemma swap_proof : sound stack_step swap_spec.
Proof. list_solver. Qed.
