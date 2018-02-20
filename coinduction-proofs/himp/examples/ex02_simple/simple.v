Require Export himp_steps.
Require Export himp_tactics.

Set Implicit Arguments.

Require Import ZArith.
Require Import List.

Hint Extern 0 (KInt _ = KInt _) => f_equal : done_hints.
Hint Extern 0 (ECon _ = ECon _) => f_equal : done_hints.

Ltac use_cfg_assumptions :=
  match goal with
    | [H : kcell ?v = _ |- _] =>
      is_var v; destruct v; simpl in * |- ;
      rewrite H in * |- *;clear H
    | [H : exists _ : Map _ _ , _ |- _] =>
      decompose record H; clear H
    | [H : _ /\ _  |- _ ] => destruct H
    | [H : ?l ~= _ |- ?G] =>
         match G with
         | context [?l] => fail 1
         | _ => is_var l;rewrite H in * |- *;clear H l
         end
   end.

Ltac trans_use_result ::=
  try solve[intros;eapply ddone;assumption]
  || (apply use_returning;do 6 intro;try use_expose_frame;intros)
     ; repeat use_cfg_assumptions.

Ltac start_proving ::=
  let get_cfg_assumptions := (intros;repeat use_cfg_assumptions) in
  get_cfg_assumptions;apply proved_sound;destruct 1;
  simpl in * |-;get_cfg_assumptions.

Definition simple_fun (R : Spec kcfg) (d:Defn) : forall (args : list KResult) (ret : KResult), Prop :=
  match d with
    FunDef name formals body =>
    fun args ret =>
    forall krest store stack heap funs otherfuns mark,
      funs ~= kra (KId name) kdot |-> kra (KDefn d) kdot :* otherfuns ->
      R (KCfg (kra (ECall name (map KResultToExp args)) krest)
              store stack heap funs mark)
        (fun c' => match c' with
           | KCfg (kra r' krest') store' stack' heap' funs' mark' =>
               r' = KResultToK ret /\ krest' = krest /\ store' ~= store
               /\ heap' ~= heap /\ funs ~= funs' /\ (mark' >= mark)%Z
           | _ => False
         end)
   end.

Ltac simple_run    := generic_run    trans_tac step_solver done_solver split_tac.
Ltac simple_solver := generic_solver trans_tac step_solver done_solver split_tac.
Ltac simple_step   := generic_step   trans_tac step_solver             split_tac.