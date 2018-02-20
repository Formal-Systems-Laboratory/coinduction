Require Import ZArith.
Require Import List.
Require Import FMapPositive.
Require Import String.
Open Scope string_scope.

Require Import domains.

(* Define the transition relation.
   This is split into a separate file because 
   a bug in Proof General prevents interactively
   advancing past definitions as long as the
   Inductive block.
 *)

Set Implicit Arguments.

Notation exp_step step a b :=
  (forall env henv lenv,
     step (KCfg a env henv lenv)
          (KCfg b env henv lenv)) (only parsing).

Notation exp1_step step a b := (forall rest, exp_step step (kra a rest) (kra b rest)) (only parsing).

Inductive pat1 (A : Set) : Set :=
  | wild : pat1 A
  | read : A -> pat1 A
  | write : A -> A -> pat1 A.
Arguments wild {A}.

Inductive cell : Set :=
  | k_cell : pat1 (list kitem) -> cell
  | env_cell : pat1 (Map string Z) -> cell 
  | heap_cell : pat1 (Map Z Z) -> cell
  | code_cell : pat1 (Map Z Stmt) -> cell
  .

Inductive pat : Set :=
  | KPat : pat1 (list kitem) -> pat1 (Map string Z) ->
           pat1 (Map Z Z) -> pat1 (Map Z Stmt) -> pat
  .

Definition ext (c : cell) (p : pat) : pat :=
  match p with
    | KPat k env heap code => 
      match c with
        | k_cell k => KPat k env heap code 
        | env_cell env =>  KPat k env heap code 
        | heap_cell heap =>  KPat k env heap code 
        | code_cell code =>  KPat k env heap code 
      end
  end.

Definition arg (A : Set) (p : pat1 A) (k : A -> A -> Prop) : Prop :=
  match p with
    | wild => forall x, k x x
    | read x => k x x
    | write x1 x2 => k x1 x2
  end.

Definition mk_step (step : kcfg -> kcfg -> Prop) (p : pat) : Prop :=
  match p with
    | KPat k env heap code =>
      arg k (fun k1 k2 =>
      arg env (fun e1 e2 =>
      arg heap (fun h1 h2 =>
      arg code (fun c1 c2 =>
        step (KCfg k1 e1 h1 c1) (KCfg k2 e2 h2 c2)))))
  end.

Fixpoint mkpat (step : kcfg -> kcfg -> Prop) (p : pat)
   (members : list cell) : Prop :=
  match members with
    | nil => mk_step step p
    | c :: cells' => mkpat step (ext c p) cells'
  end.

Definition krule (step : kcfg -> kcfg -> Prop) (members : list cell) : Prop :=
  mkpat step (KPat wild wild wild wild) members.

Notation "'[' x ';' .. ';' y ']'" := (cons x (.. (cons y nil) ..)).

Coercion KExp : Exp >-> kitem.
Coercion KBExp : BExp >-> kitem.
Coercion KStmt : Stmt >-> kitem.

Definition eval1 x y rest  := (k_cell (write (kra x rest)
                                           (kra y rest))).
Definition heat e h1 h2 rest := (k_cell (write (kra e rest)
                                               (kra h1 (kra h2 rest)))).

Definition kcell_step step k1 k2 :=
  forall env heap lenv,
    step (KCfg k1 env heap lenv)
         (KCfg k2 env heap lenv).

(* Definition heat_step step e h1 h2 rest :=
  krule step [heat e h1 h2 rest]. *)
Definition heat_step step e h1 h2 rest :=
  kcell_step step (kra e rest) (kra h1 (kra h2 rest)).

Definition heat_exp step e h1 h2 rest :=
  isEVal h1 = false -> heat_step step e h1 h2 rest.
Definition heat_bool step e h1 h2 rest :=
  isBool h1 = false -> heat_step step e h1 h2 rest.

Notation heat_exp_1 step con :=
  (forall rest x, heat_exp step (con x) x (KFreezeE con) rest).
Notation heat_exp_l step con :=
  (forall rest x y, heat_exp step (con x y) x (KFreezeE (fun x => con x y)) rest).
Notation heat_exp_r step con :=
  (forall rest x y, heat_exp step (con x y) y (KFreezeE (fun y => con x y)) rest).

Notation heat_bool_1 step con :=
  (forall rest x, heat_bool step (con x) x (KFreezeB con) rest).
Notation heat_bool_l step con :=
  (forall rest x y, heat_bool step (con x y) x (KFreezeB (fun x => con x y)) rest).
Notation heat_bool_r step con :=
  (forall rest x y, heat_bool step (con x y) y (KFreezeB (fun y => con x y)) rest).

(*
Notation eval_rule step e1 e2 :=
  (forall rest, krule step [eval1 e1 e2 rest]).
 *)
Notation eval_rule step e1 e2 :=
  (forall rest, kcell_step step (kra e1 rest) (kra e2 rest)).

Definition stmt1 s rest  := (k_cell (write (kra s rest) rest)).
Definition stmt_step s1 s2 rest  := (k_cell (write (kra s1 rest) (kra s2 rest))).

Generalizable Variables rest env erest henv hrest lenv x y i j v r e b s.
Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  (* evaluation in K *)
  | k_amb_left : `(eval_rule kstep (EAmb x y) x)
  | k_amb_right : `(eval_rule kstep (EAmb x y) y)
  | k_plus : `(eval_rule kstep (EPlus (ECon i) (ECon j)) (ECon (Zplus i j)))
  | k_minus : `(eval_rule kstep (EMinus (ECon i) (ECon j)) (ECon (Zminus i j)))
  | k_div : `(Zneq_bool 0%Z j = true ->
              eval_rule kstep (EDiv (ECon i) (ECon j)) (ECon (Zdiv i j)))
  | k_le : `(eval_rule kstep (BLe (ECon i) (ECon j)) (BCon (Zle_bool i j)))
  | k_eq : `(eval_rule kstep (BEq (ECon i) (ECon j)) (BCon (i =? j)%Z))
  | k_not : `(eval_rule kstep (BNot (BCon b)) (BCon (negb b)))
  | k_and_t : `(eval_rule kstep (BAnd (BCon true) b) b)
  | k_and_f : `(eval_rule kstep (BAnd (BCon false) b) (BCon false))

  | k_skip: `(kcell_step kstep (kra Skip rest) rest)
  | k_if_t : `(eval_rule kstep (SIf (BCon true) s1 s2) s1)
  | k_if_f : `(eval_rule kstep (SIf (BCon false) s1 s2) s2)
  | k_while : `(eval_rule kstep (SWhile b s)
                                (SIf b (Seq s (SWhile b s)) Skip))
  (* evaluation rules *)
  | k_lookup : `(env ~= (x |-> i :* erest) ->
                 krule kstep [eval1 (EVar x) (ECon 1) rest
                             ;env_cell (write env (x |-> i :* erest))])
  | k_load : `(henv ~= (i |-> j :* hrest) ->
                 krule kstep [eval1 (ELoad (ECon i)) (ECon j) rest
                             ;heap_cell (read henv)])
  | k_assign : `(env ~= (x |-> v :* erest) ->
                 krule kstep [stmt1 (SAssign x (ECon i)) rest
                             ;env_cell (write env (x |-> i :* erest))])
  | k_hassign : `(henv ~= (i |-> v :* hrest) ->
                 krule kstep [stmt1 (HAssign (ECon i) (ECon j)) rest
                             ;heap_cell (write henv (i |-> j :* hrest))])
  | k_jump : `(forall l,
                 lenv ~= (l |-> s :* erest) ->
                 krule kstep [k_cell (write (kra (Jump (ECon l)) rest)
                                            (kra (KStmt s) kdot))
                             ;code_cell (read lenv)])
  (* heating and cooling *)
  | k_cool_e : `(kcell_step kstep (kra (ECon i) (kra (KFreezeE e) rest))
                                  (kra (e (ECon i)) rest))
  | k_cool_b : `(kcell_step kstep (kra (BCon b) (kra (KFreezeB e) rest))
                                  (kra (e (BCon b)) rest))

  (* unary *)
  | k_heat_load : heat_exp_1 kstep ELoad
  (* plus *)
  | k_heat_plus_l : heat_exp_l kstep EPlus
  | k_heat_plus_r : heat_exp_r kstep EPlus
  (* minus *)
  | k_heat_minus_l : heat_exp_l kstep EMinus
  | k_heat_minus_r : heat_exp_r kstep EMinus
  (* div *)
  | k_heat_div_l : heat_exp_l kstep EDiv
  | k_heat_div_r : heat_exp_r kstep EDiv
  (* le is seqstrict *)
  | k_heat_le_l : heat_exp_l kstep BLe
  | k_heat_le_r : heat_exp_r kstep BLe
  (* eq is seqstrict *)
  | k_heat_eq_l : heat_exp_l kstep BEq
  | k_heat_eq_r : heat_exp_r kstep BEq
  (* and is only strict in left argument *)
  | k_heat_not : heat_bool_1 kstep BNot
  | k_heat_and : heat_bool_l kstep BAnd
  (* assign *)
  | k_heat_assign : heat_exp_r kstep SAssign
  (* hassign *)
  | k_heat_hassign_l : heat_exp_l kstep HAssign
  | k_heat_hassign_r : heat_exp_r kstep HAssign
  (* jump *)
  | k_heat_jump : heat_exp_1 kstep Jump
  (* if *)
  | k_heat_if : `(heat_bool kstep (SIf b s1 s2) b
                            (KFreezeB (fun c => SIf c s1 s2)) rest)
  (* seq *)
  | k_heat_seq : `(heat_step kstep (Seq s1 s2) s1 s2 rest)
  .
