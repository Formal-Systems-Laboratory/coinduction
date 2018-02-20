Require Import list_examples.

Definition append_code :=
  Over::If (Over::While (Plus1++Dup 0::Load::Dup 0::nil) Nip
  ::Drop::Store::nil) Nip::Ret::nil.

Inductive append_spec : cfg -> (cfg -> Prop) -> Prop :=
  | append_claim : forall lx ly, fun_claim append_spec
    "append" append_code
      2 (fun y x => rep_list lx x :* rep_list ly y)
      1 (rep_list (lx++ly))
  | loop_claim : forall lx a lp ly, loop_claim append_spec
    0 append_code
      3 (fun p y x => constraint (p <> 0) :*
         rep_list ly y :* rep_seg lx p x :* p |-> a :*
         existsP p', p + 1 |-> p' :* rep_list lp p')
      1 (rep_list (lx++a::lp++ly)).

Lemma append_proof : sound stack_step append_spec.
Proof. list_solver;
rewrite app_ass in * |- *;
list_run. Qed.