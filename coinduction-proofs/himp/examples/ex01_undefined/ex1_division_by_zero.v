Require Import undefined.

Require Import List.

Definition division_by_zero_code :=
  Seq (SAssign "x" (ECon 0))
      (SReturn (EDiv (ECon 3) (EVar "x"))).

Lemma division_by_zero_stuck : forall c,
 kcell c = kra (KStmt division_by_zero_code) kdot -> 
  forall v m, store c ~= "x" s|-> v :* m ->
  sound kstep (gets_stuck c).
Proof. undefined_solver. Qed.
