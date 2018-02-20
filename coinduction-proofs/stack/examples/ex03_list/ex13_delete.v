Require Import list_examples.

Fixpoint delete v l :=
  match l with
    | nil => nil
    | (x :: l') => if Z.eqb x v
        then delete v l'
        else x :: delete v l'
  end.
Arguments delete v l : simpl nomatch.

Definition z_test_eq (a b : Z) := if Z.eqb a b then 1 else 0.

Definition delete_code :=
  Swap::While (Dup 0::If (Dup 0::Load::Dup 2::Binop z_test_eq::nil)
                         (Dup 0::nil)::nil)
         (Dup 0::Dealloc::Plus1++Dup 0::Load::Swap::Dealloc::nil)
  ::Dup 0::If
    (Swap::Over::
     While (Dup 0::Plus1++Load::Dup 0::nil)
       (Dup 0::Load::Dup 3::Binop z_test_eq
        ::If (Over::Plus1++Store::nil) Nip::nil)
     ::Drop::Drop::Drop::nil)
    (Swap::Drop::nil)
  ::Ret::nil.

Inductive delete_spec : Spec cfg :=
  delete_claim : forall l v, fun_claim delete_spec
  "delete" delete_code
    2 (fun v' p => constraint (v'=v) :* rep_list l p)
    1 (rep_list (delete v l))
 |init_loop : forall l v, loop_claim delete_spec
  0 delete_code
    2 (fun p v' => constraint (v'=v) :* rep_list l p)
    1 (rep_list (delete v l))
 |run_loop : forall A x v B , loop_claim delete_spec
  1 delete_code
    3 (fun p v' r => constraint (v'=v) :* rep_seg A p r
       :* constraint (p <> 0) :* p |-> x :* constraint (x <> v)
       :* existsP q, (p+1) |-> q :* rep_list B q)
    1 (rep_list (A++x::delete v B)).

Ltac eqb_solve := intros; match goal with [|- context [?a =? ?b]]
  => destruct (Z.eqb_spec a b);intuition congruence end.
Lemma z_test_eql : forall z v, z_test_eq z v = 0 <-> z <> v.
Proof. unfold z_test_eq;eqb_solve. Qed.
Lemma z_test_neq : forall z v, z_test_eq z v <> 0 <-> z = v.
Proof. unfold z_test_eq;eqb_solve. Qed.
Lemma delete_eq v x l : x = v -> delete v (x::l) = delete v l.
Proof. unfold delete;eqb_solve. Qed.
Lemma delete_ne v x l : x<>v -> delete v (x::l) = x::delete v l.
Proof. unfold delete;eqb_solve. Qed.

Create HintDb delete_rules discriminated.
Hint Rewrite z_test_eql z_test_neq app_ass : delete_rules.
Hint Rewrite delete_eq delete_ne using assumption : delete_rules.

Lemma delete_proof : sound stack_step delete_spec.    
Proof. list_solver;repeat progress
  (autorewrite with delete_rules in * |- *;list_run). Qed.
