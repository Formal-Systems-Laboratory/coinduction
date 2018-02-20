Require Import simple.

Require Import List.
Require Import ZArith.

Definition f_code :=
  SReturn (EPlus (EVar "x") (EPlus (EVar "y") (EMult (EVar "x") (EVar "y")))).

Definition comm_assoc_code :=
  SIf
    (BAnd (BEq (ECall "f" (EVar "x" :: EVar "y" :: nil))
               (ECall "f" (EVar "y" :: EVar "x" :: nil)))
          (BEq (ECall "f" (EVar "x" :: ECall "f" (EVar "y" :: EVar "z" :: nil) :: nil))
               (ECall "f" (ECall "f" (EVar "x" :: EVar "y" :: nil) :: EVar "z" :: nil))))

    (SReturn (ECon 1))
    (SReturn (ECon 0)).

Require Import Setoid.

Lemma comm_assoc_spec : forall c, kcell c = kra (KStmt comm_assoc_code) kdot -> 
  forall xv yv zv, store c ~=
    ("x" s|-> KInt xv :* "y" s|-> KInt yv :* "z" s|-> KInt zv) ->
    functions c ~= ("f" s|-> FunDef "f" ["x";"y"] f_code) ->
  sound kstep (returns c 1).
Proof.
simple_solver.
Qed.
