Require Import list_examples.

Definition length_code :=
  Push 0::Swap::While (Dup 0::nil)
   (Swap::Plus1++Swap::Plus1++Load::nil)::Drop::Ret::nil.

Fixpoint zlength {A} (l : list A) :=
  match l with
    | nil => 0
    | _ :: l' => (1 + zlength l')
  end.
Inductive length_spec : Spec cfg :=
  length_claim : forall H l, fun_claim length_spec
  "length" length_code
    1 (fun p => asP H (rep_list l p))
    1 (fun n => constraint (n = zlength l) :* litP H)
 |loop_claim : forall H l n, loop_claim length_spec
  0 length_code
    2 (fun p k => constraint (k = n) :* asP H (rep_list l p))
    1 (fun k' => constraint (k' = n + zlength l) :* litP H).

Lemma length_proof : sound stack_step length_spec.
Proof. list_solver. Qed.