Require Import simple.

Require Import List.
Require Import ZArith.

Definition minimum_code :=
  SIf (BLt (EVar "x") (EVar "y"))
      (SReturn (EVar "x"))
      (SReturn (EVar "y")).

Hint Resolve Z.min_l Z.min_r : done_hints.

Lemma minimum_spec :
  forall c, kcell c = kra (KStmt minimum_code) kdot -> 
  forall xv yv m, store c ~=
    ("x" s|-> KInt xv :* "y" s|-> KInt yv :* m) ->
  sound kstep (returns c (Z.min xv yv)).
Proof. simple_solver. Qed.
