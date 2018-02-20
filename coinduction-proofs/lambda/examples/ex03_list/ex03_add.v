Require Import list_examples.

Definition add_body := Ref (Cons (Var 1) (Var 0)).
                                                                       
Inductive add_spec : Spec cfg :=
  add_claim : forall x r env, exp_val add_spec
  add_body (r::x::env) emptyP (list_seg (x::nil) r).

Lemma add_proof : sound lam_step add_spec.
Proof. list_solver. Qed.