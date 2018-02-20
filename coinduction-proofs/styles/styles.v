Require Export ZArith.
Require Export String.
Require Export maps.

Require Export proof.

Open Scope string_scope.

Set Implicit Arguments.

Inductive Exp : Set :=
   BCon : bool -> Exp
 | EVar : string -> Exp
 | ECon : Z -> Exp
 | EGt : Exp -> Exp -> Exp
 | EPlus : Exp -> Exp -> Exp
with Stmt : Set :=
   SAssign : string -> Exp -> Stmt
 | Seq : Stmt -> Stmt -> Stmt
 | SIf : Exp -> Stmt -> Stmt -> Stmt
 | Skip : Stmt
 | SWhile : Exp -> Stmt -> Stmt
 .

Ltac step_solver := fail.
Ltac trans_solver := econstructor(equate_maps).
Ltac run :=
  first [eapply dtrans;[trans_solver|];try run
        |solve[intros;apply ddone;eauto]
        |eapply dstep;[step_solver|];instantiate;simpl;try run
        ].

(*
Inductive loop_spec : (Stmt * Map string Z) -> ((Stmt * Map string Z) -> Prop) -> Prop :=
  | loop_claim : forall store n rest, store ~= "n" |-> n ->
      loop_spec (Seq (SWhile (EGt (EVar "n") (ECon 0%Z)) (SAssign "n" (EPlus (EVar "n") (ECon (-1)%Z)))) rest, store)
     (fun c => fst c = rest /\ exists n, (n <= 0)%Z /\ snd c ~= "n" |-> n).
 *)

Inductive loop_spec {prog : Set} (wrap : Stmt -> prog -> prog)
    : (prog * Map string Z) -> ((prog * Map string Z) -> Prop) -> Prop :=
  | loop_claim : forall store n rest, store ~= "n" |-> n ->
      loop_spec wrap (wrap (SWhile (EGt (EVar "n") (ECon 0%Z)) (SAssign "n" (EPlus (EVar "n") (ECon (-1)%Z)))) rest, store)
     (fun c => fst c = rest /\ exists n, (n <= 0)%Z /\ snd c ~= "n" |-> n).

Inductive loop_spec_inf {prog : Set} (wrap : Stmt -> prog -> prog)
    : (prog * Map string Z) -> ((prog * Map string Z) -> Prop) -> Prop :=
  | loop_claim_inf : forall store n rest, store ~= "n" |-> n ->
      loop_spec_inf wrap (wrap (SWhile (EGt (ECon 1%Z) (ECon 0%Z)) (SAssign "n" (EPlus (EVar "n") (ECon (-1)%Z)))) rest, store)
     (fun c => False).

Ltac trans_solver ::=
     solve[refine (loop_claim _ _ _);equate_maps] ||
     solve[refine (loop_claim_inf _ _ _);equate_maps].

Ltac example_proof :=
  apply proved_sound;destruct 1;
  eapply sstep;[step_solver|];instantiate;simpl;
  run;
  match goal with
  |[|- context [(?n >? 0)%Z]] => destruct (Z.gtb_spec n 0)
  end;
  run.

(* Now three styles of semantics *)

(* First small step *)
Module small_step.

Inductive exp_step : (Exp * Map string Z) -> (Exp * Map string Z) -> Prop :=
  (* Ordered so we should use the earliest constructor to make progress *)
  | eval_var : forall v z rest store, store ~= v |-> z :* rest ->
      exp_step (EVar v, store) (ECon z, store)
  | eval_gt : forall z1 z2 store,
      exp_step (EGt (ECon z1) (ECon z2), store) (BCon (Z.gtb z1 z2), store)
  | eval_plus : forall z1 z2 store,
      exp_step (EPlus (ECon z1) (ECon z2), store) (ECon (Z.add z1 z2), store)
  | eval_gt_r : forall z e1 e2 store1 store2,
      exp_step (e1, store1) (e2, store2) ->
      exp_step (EGt (ECon z) e1, store1) (EGt (ECon z) e2, store2)
  | eval_gt_l : forall e1 e2 r store1 store2,
      exp_step (e1, store1) (e2, store2) ->
      exp_step (EGt e1 r, store1) (EGt e2 r, store2)
  | eval_plus_r : forall z e1 e2 store1 store2,
      exp_step (e1, store1) (e2, store2) ->
      exp_step (EPlus (ECon z) e1, store1) (EPlus (ECon z) e2, store2)
  | eval_plus_l : forall e1 e2 r store1 store2,
      exp_step (e1, store1) (e2, store2) ->
      exp_step (EPlus e1 r, store1) (EPlus e2 r, store2)
  .

Inductive step : (Stmt * Map string Z) -> (Stmt * Map string Z) -> Prop :=
  | exec_assign : forall v z z0 rest store, store ~= v |-> z0 :* rest ->
      step (SAssign v (ECon z), store) (Skip, (v |-> z :* rest))
  | exec_seq : forall s2 store,
      step (Seq Skip s2, store) (s2, store)
  | exec_if : forall b t e store,
      step (SIf (BCon b) t e, store) (if b then t else e, store)
  | exec_while : forall cond body store,
      step (SWhile cond body, store) (SIf cond (Seq body (SWhile cond body)) Skip, store)
  | exec_assign_1 : forall e1 e2 store1 store2 v,
      exp_step (e1, store1) (e2, store2) ->
      step (SAssign v e1, store1) (SAssign v e2, store2)
  | exec_seq_1 : forall s1 s2 store1 store2 r,
      step (s1, store1) (s2, store2) ->
      step (Seq s1 r, store1) (Seq s2 r, store1)
  | exec_if_1 : forall c1 store1 c2 store2 t e,
      exp_step (c1, store1) (c2, store2) ->
      step (SIf c1 t e, store1) (SIf c2 t e, store2)
 .

Create HintDb step_db discriminated.
Hint Extern 1 (_ ~= _) => equate_maps : step_db.
Hint Constructors step exp_step : step_db.

Ltac step_solver ::= solve[eauto 20 with step_db].

Lemma example : sound step (loop_spec Seq).
Proof. example_proof. Qed.

Lemma example_inf : sound step (loop_spec_inf Seq).
Proof. example_proof. Qed.

End small_step.

(* Now evaluation context *)
Module evaluation_contexts.

Inductive context : Set -> Set :=
   Top : context Stmt
 | EGt_left : Exp -> context Exp -> context Exp
 | EGt_right : Z -> context Exp -> context Exp
 | EPlus_left : Exp -> context Exp -> context Exp
 | EPlus_right : Z -> context Exp -> context Exp
 | SAssign_2 : string -> context Stmt -> context Exp
 | Seq_left : Stmt -> context Stmt -> context Stmt
 | SIf_1 : Stmt -> Stmt -> context Stmt -> context Exp
 .

Fixpoint plug {s : Set} (c : context s) : s -> Stmt :=
  match c with
  | Top => fun t => t
  | EGt_left r c => fun l => plug c (EGt l r)
  | EGt_right l c => fun r => plug c (EGt (ECon l) r)
  | EPlus_left r c => fun l => plug c (EPlus l r)
  | EPlus_right l c => fun r => plug c (EPlus (ECon l) r)
  | SAssign_2 v c => fun t => plug c (SAssign v t)
  | Seq_left r c => fun l => plug c (Seq l r)
  | SIf_1 t e c => fun v => plug c (SIf v t e)
 end.

Inductive step : (Stmt * Map string Z) -> (Stmt * Map string Z) -> Prop :=
  | eval_var : forall c v z rest store, store ~= v |-> z :* rest ->
      step (plug c (EVar v), store) (plug c (ECon z), store)
  | eval_gt : forall c z1 z2 store,
      step (plug c (EGt (ECon z1) (ECon z2)), store) (plug c (BCon (Z.gtb z1 z2)), store)
  | eval_plus : forall c z1 z2 store,
      step (plug c (EPlus (ECon z1) (ECon z2)), store) (plug c (ECon (Z.add z1 z2)), store)
  | exec_assign : forall c v z z0 rest store, store ~= v |-> z0 :* rest ->
      step (plug c (SAssign v (ECon z)), store) (plug c Skip, (v |-> z :* rest))
  | exec_seq : forall c s2 store,
      step (plug c (Seq Skip s2), store) (plug c s2, store)
  | exec_if : forall c b t e store,
      step (plug c (SIf (BCon b) t e), store) (plug c (if b then t else e), store)
  | exec_while : forall c cond body store,
      step (plug c (SWhile cond body), store) (plug c (SIf cond (Seq body (SWhile cond body)) Skip), store)
 .

Ltac split_ctx ctx t k :=
  match t with
  (* stop at redexes *)
  | (Seq Skip ?rest) => k ctx t
  | (SWhile _ _) => k ctx t
  | (SIf (BCon _) _ _) => k ctx t
  | (EGt (ECon _) (ECon _)) => k ctx t
  | (EVar _) => k ctx t
  | (SAssign _ (ECon _)) => k ctx t
  | (EPlus (ECon _) (ECon _)) => k ctx t
  (* else enter *)
  | (Seq ?l ?r) => let ctx' := constr:(Seq_left r ctx) in split_ctx ctx' l k
  | (SIf ?c ?t ?e) => let ctx' := constr:(SIf_1 t e ctx) in split_ctx ctx' c k
  | (EGt (ECon ?z) ?r) => let ctx' := constr:(EGt_right z ctx) in split_ctx ctx' r k
  | (EGt ?l ?r) => let ctx' := constr:(EGt_left r ctx) in split_ctx ctx' l k
  | (SAssign ?v ?e) => let ctx' := constr:(SAssign_2 v ctx) in split_ctx ctx' e k
  | (EPlus (ECon ?z) ?r) => let ctx' := constr:(EPlus_right z ctx) in split_ctx ctx' r k
  | (EPlus ?l ?r) => let ctx' := constr:(EPlus_left r ctx) in split_ctx ctx' l k
  end.
Ltac split_term t :=
  let ctx := constr:Top in split_ctx ctx t ltac:(fun c r => change t with (plug c r)).
Ltac step_solver ::=
  match goal with
  |[|- step (?t, ?store) ?P] => split_term t
  end;econstructor(equate_maps).

Lemma example : sound step (loop_spec Seq).
Proof. example_proof. Qed.

Lemma example_inf : sound step (loop_spec_inf Seq).
Proof. example_proof. Qed.

End evaluation_contexts.

(* Finally k style *)

Module k_style.

Require Import List.

Inductive kitem : Set :=
  | KExp : Exp -> kitem
  | KStmt : Stmt -> kitem
  | KFreezeZ : (Z -> kitem) -> kitem
  | KFreezeB : (bool -> kitem) -> kitem
  .

Inductive step : (list kitem * Map string Z) -> (list kitem * Map string Z) -> Prop :=
  | eval_var : forall c v z rest store, store ~= v |-> z :* rest ->
      step (KExp (EVar v) :: c, store) (KExp (ECon z) :: c, store)
  | eval_gt : forall c z1 z2 store,
      step (KExp (EGt (ECon z1) (ECon z2)) :: c, store) (KExp (BCon (Z.gtb z1 z2)) :: c, store)
  | eval_plus : forall c z1 z2 store,
      step (KExp (EPlus (ECon z1) (ECon z2)) :: c, store) (KExp (ECon (Z.add z1 z2)) :: c, store)
  | exec_assign : forall c v z z0 rest store, store ~= v |-> z0 :* rest ->
      step (KStmt (SAssign v (ECon z)) :: c, store) (KStmt Skip :: c, (v |-> z :* rest))
  | exec_skip : forall c store,
      step (KStmt Skip :: c, store) (c, store)
  | exec_seq : forall c s1 s2 store,
      step (KStmt (Seq s1 s2) :: c, store) (KStmt s1 :: KStmt s2 :: c, store)
  | exec_if : forall c b t e store,
      step (KStmt (SIf (BCon b) t e) :: c, store) (KStmt (if b then t else e) :: c, store)
  | exec_while : forall c cond body store,
      step (KStmt (SWhile cond body) :: c, store)
           (KStmt (SIf cond (Seq body (SWhile cond body)) Skip) :: c, store)

  | cool_z : forall c z f store,
      step (KExp (ECon z) :: KFreezeZ f :: c, store)
           (f z :: c, store)
  | cool_b : forall c b f store,
      step (KExp (BCon b) :: KFreezeB f :: c, store)
           (f b :: c, store)
  | heat_gt_l : forall c e1 e2 store,
      step (KExp (EGt e1 e2) :: c, store)
           (KExp e1 :: KFreezeZ (fun z => KExp (EGt (ECon z) e2)) :: c, store)
  | heat_gt_r : forall c z1 e2 store,
      step (KExp (EGt (ECon z1) e2) :: c, store)
           (KExp e2 :: KFreezeZ (fun z2 => KExp (EGt (ECon z1) (ECon z2))) :: c, store)
  | heat_plus_l : forall c e1 e2 store,
      step (KExp (EPlus e1 e2) :: c, store)
           (KExp e1 :: KFreezeZ (fun z => KExp (EPlus (ECon z) e2)) :: c, store)
  | heat_plus_r : forall c z1 e2 store,
      step (KExp (EPlus (ECon z1) e2) :: c, store)
           (KExp e2 :: KFreezeZ (fun z2 => KExp (EPlus (ECon z1) (ECon z2))) :: c, store)
  | heat_assign : forall c v e store,
      step (KStmt (SAssign v e) :: c, store)
           (KExp e :: KFreezeZ (fun z => KStmt (SAssign v (ECon z))) :: c, store)
  | heat_if : forall c b t e store,
      step (KStmt (SIf b t e) :: c, store)
           (KExp b :: KFreezeB (fun b => KStmt (SIf (BCon b) t e)) :: c, store)
 .

Ltac step_solver ::= econstructor(equate_maps).

Lemma example : sound step (loop_spec (fun s c => KStmt s :: c)).
Proof. example_proof. Qed.

Lemma example_inf : sound step (loop_spec_inf (fun s c => KStmt s :: c)).
Proof. example_proof. Qed.

End k_style.