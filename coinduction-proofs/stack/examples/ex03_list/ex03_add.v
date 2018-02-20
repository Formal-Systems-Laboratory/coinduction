Require Import list_examples.

Definition add_code :=
  Alloc 2::Swap::Over::Store::Swap::Over::Plus1++Store::Ret::nil.

Inductive add_spec : Spec cfg :=
  add_claim : forall x H p l, fun_claim add_spec
  "add" add_code
    2 (fun a b => constraint (a = x) :* constraint (b = p)
      :* asP H (rep_list l b))
    1 (fun r => rep_seg (x::nil) p r :* litP H).

Lemma add_proof : sound stack_step add_spec.
Proof. list_solver. Qed.
