Require Import list_examples.

Definition length_code :=
 Dup 0::If (Plus1++Load::Call "length"::Plus1) nil::Ret::nil.

Fixpoint zlength {A} (l : list A) :=
  match l with
    | nil => 0
    | _ :: l' => 1 + zlength l'
  end.
Inductive length_spec : Spec cfg :=
  length_claim : forall H l, fun_claim length_spec
  "length" length_code
    1 (fun p => asP H (rep_list l p))
    1 (fun n => constraint (n = zlength l) :* litP H).

Lemma length_proof : sound stack_step length_spec.
Proof. list_solver. Qed.