Require Import simple.

Require Import List.
Require Import ZArith.

Definition mult_code :=
  SIf (BEq (EVar "x") (ECon 0))
      (SReturn (ECon 0))
   (SIf (BLt (EVar "x") (ECon 0))
        (SReturn (ENeg (ECall "multiplication_by_addition"
                          (ENeg (EVar "x") :: EVar "y" :: nil))))
        (SReturn (EPlus (EVar "y")
                        (ECall "multiplication_by_addition"
                              (EMinus (EVar "x") (ECon 1) :: EVar "y" :: nil))))).

Definition mult_fun :=
  FunDef "multiplication_by_addition" ("x" :: "y" :: nil) mult_code.

Inductive mult_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  mult_claim : forall c, kcell c = kra (KStmt mult_code) kdot -> 
    forall xv yv m, store c ~=
      ("x" s|-> KInt xv :* "y" s|-> KInt yv :* m) ->
    forall f, functions c ~=
      ("multiplication_by_addition" s|-> KDefn mult_fun :* f) ->
    mult_spec c (returning c (xv * yv)).
Lemma mult_sound : sound kstep mult_spec.
Proof. simple_solver. Qed.
