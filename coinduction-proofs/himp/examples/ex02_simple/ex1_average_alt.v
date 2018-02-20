Require Import simple.

Require Import List.
Require Import ZArith.

Definition average_fun :=
  FunDef "average" ["x";"y";"z"]
  (Seq (Decl "sum")
  (Seq (SAssign "sum" (EPlus (EPlus (EVar "x") (EVar "y")) (EVar "z")))
       (SReturn (EDiv (EVar "sum") (ECon 3))))).

Inductive average_spec : Spec kcfg :=
  | average_claim : forall xv yv zv,
      simple_fun average_spec average_fun [Int xv; Int yv; Int zv]
         (Int ((xv + yv + zv)  / 3)%Z).
Lemma average_proof : sound kstep average_spec.
Proof. simple_solver. Qed.