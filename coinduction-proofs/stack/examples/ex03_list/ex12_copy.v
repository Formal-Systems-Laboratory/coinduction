Require Import list_examples.

Definition init_head :=
  Over::Load::Over::Store::Swap::Plus1++Load::nil.
Definition copy_code := Dup 0::
  If (Alloc 2::Swap::Over::init_head++
      While (Dup 0::nil)
        (Swap::Alloc 2::Dup 0::Rot++Plus1++Store::init_head)
    ::Swap::Plus1++Store::nil) nil
  ::Ret::nil.

Inductive copy_spec : Spec cfg :=
  copy_claim : forall H l, fun_claim copy_spec
  "copy" copy_code
    1 (fun p => asP H (rep_list l p))
    1 (fun r => rep_list l r :* litP H)
 |loop_claim : forall H l1 x v l, loop_claim copy_spec
  0 copy_code
    3 (fun y q r => constraint (q <> 0)
       :* rep_seg l1 q r :* q |-> x :* q+1 |-> v
       :* asP H (rep_list l y))
    1 (fun r => rep_list (l1++x::l) r :* litP H).

Lemma copy_proof : sound stack_step copy_spec.
Proof. list_solver;
rewrite app_ass in * |-;
list_run. Qed.
