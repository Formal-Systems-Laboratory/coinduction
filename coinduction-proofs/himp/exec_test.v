(*
  This is a dummy file for interactively observing how
  the step_solver tactics work on a concrete program.
  (especially that it's not getting stuck in the semantics,
   and that the example configuration is well-formed).
 *)

Require Import himp_steps.
Require Import himp_syntax_sugar.
Require Import himp_tactics.

Require Import ZArith.

Ltac step_solver :=
  econstructor (solve[simpl;eauto;equate_maps;eauto]).

(*
Ltac step_solver := econstructor (solve[simpl;try reflexivity;eauto with step_hints]);idtac.
*)

Goal
 reaches kstep
      (KCfg (kra (SWhile (BLt (EVar "x") (ECon 13))
                         (Seq (SAssign "cur" EAlloc)
                         (Seq (HAssign (EVar "cur")
                                       (EBuild
                                          ("val" s|-> KId "x"
                                          :* "next" s|-> KId "prev")))
                         (Seq (SAssign "prev" (EVar "cur"))
                              (SAssign "x" (EPlus (EVar "x") (ECon 1)))))))
                 kdot)
       ("x" s|-> KInt 10 :* "cur" s|-> (KUndef undef) :* "prev" s|-> KInt 0 :* mapEmpty)
       nil
       mapEmpty
       mapEmpty
       1)
      (fun c => kcell c = kdot).

Set Printing Coercions.

do 40 (eapply rstep;[step_solver|]).
do 40 (eapply rstep;[step_solver|]).
do 40 (eapply rstep;[step_solver|]).
do 9 (eapply rstep;[step_solver|]).
apply rdone. reflexivity.
Qed.
