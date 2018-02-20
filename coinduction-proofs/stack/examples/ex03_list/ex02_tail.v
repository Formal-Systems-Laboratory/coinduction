Require Import list_examples.

Definition tail_code := Plus1++Load::Ret::nil.

Inductive tail_spec : Spec cfg :=
  tail_claim : forall H x y l, fun_claim tail_spec
  "tail" (Plus1++Load::Ret::nil)
    1 (fun p => asP H (rep_seg (x::nil) y p :* rep_list l y))
    1 (fun p => constraint (p = y) :* litP H).

Lemma tail_proof : sound stack_step tail_spec.
Proof. list_solver. Qed.
