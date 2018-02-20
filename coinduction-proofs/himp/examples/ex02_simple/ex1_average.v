Require Import simple.

Require Import List.
Require Import ZArith.

Definition average_code :=
  Seq (SAssign "sum" (EPlus (EPlus (EVar "x") (EVar "y")) (EVar "z")))
      (SReturn (EDiv (EVar "sum") (ECon 3))).

Lemma average_spec :
  forall c, kcell c = kra (KStmt average_code) kdot -> 
  forall xv yv zv sv m, store c ~=
    ("x" s|-> KInt xv :* "y" s|-> KInt yv :* "z" s|-> KInt zv :*
     "sum" s|-> sv :* m) ->
  sound kstep (returns c ((xv + yv + zv)  / 3)%Z).
Proof. simple_solver. Qed.
