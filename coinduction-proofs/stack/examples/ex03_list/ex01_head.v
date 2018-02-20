Require Import list_examples.

Definition head_code := Load::Ret::nil.

Inductive head_spec : Spec cfg :=
  head_claim : forall H x l, fun_claim head_spec
  "head" head_code
    1 (fun p => asP H (rep_list (x::l) p))
    1 (fun p => constraint (p = x) :* litP H).

Lemma head_proof : sound stack_step head_spec.
Proof. list_solver. Qed.