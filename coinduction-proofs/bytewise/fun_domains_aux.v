Require Import String.
Require Import ZArith.
Require Import List.
Require Import fun_domains.

Set Implicit Arguments.

(* Basic configuration definition *)
Structure kcfg := KCfg {
  kcell : k;
  store : Map k k;
  stack : list Frame;
  heap : Map k k;
  functions : Map k k
  }.

(* Coercions needed because generated freezers
   don't have contents wrapped into kitem *)
Coercion KExp : Exp >-> kitem.
Coercion KStmt : Stmt >-> kitem.

(* Functions for the step definitions *)
Definition kcell_step step k1 k2 :=
  forall env stk heap funs,
    step (KCfg k1 env stk heap funs)
         (KCfg k2 env stk heap funs).
(* Definition heat_step step e h1 h2 rest :=
  krule step [heat e h1 h2 rest]. *)
Definition heat_step step e h1 h2 rest :=
  kcell_step step (kra e rest) (kra h1 (kra h2 rest)).

(* Recusive definitions of cooling, using in the auxiliary rules *)
(* Does not recurse into values *)
Fixpoint cool_exp_kmap (hole : Exp) (froze : Map k k) {struct froze} : Map k k:=
 match froze with
 | mapEmpty => mapEmpty
 | mapJoin l r => mapJoin (cool_exp_kmap hole l) (cool_exp_kmap hole r)
 | mapItem k (kra (KExp HOLE_Exp) kdot) => mapItem k (kra (ExpToK hole) kdot)
 | mapItem k v => mapItem k v
 end.

Fixpoint cool_exp_exp (hole : Exp) (froze : Exp) {struct froze} :=
 match froze with
 | HOLE_Exp => hole
 | ELoad e => ELoad (cool_exp_exp hole e)
 | ENeg e => ENeg (cool_exp_exp hole e)
 | EPlus l r => EPlus (cool_exp_exp hole l) (cool_exp_exp hole r)
 | EMinus l r => EMinus (cool_exp_exp hole l) (cool_exp_exp hole r)
 | EMult l r => EMult (cool_exp_exp hole l) (cool_exp_exp hole r)
 | EDiv l r => EDiv (cool_exp_exp hole l) (cool_exp_exp hole r)
 | ECall f es => ECall f
     ((fix cool_exp_exps l :=
        match l with nil => nil
        | cons e es' => cons (cool_exp_exp hole e) (cool_exp_exps es')
        end) es)
 | BLe l r => BLe (cool_exp_exp hole l) (cool_exp_exp hole r)
 | BLt l r => BLt (cool_exp_exp hole l) (cool_exp_exp hole r)
 | BEq l r => BEq (cool_exp_exp hole l) (cool_exp_exp hole r)
 | BAnd l r => BAnd (cool_exp_exp hole l) (cool_exp_exp hole r)
 | BOr l r => BOr (cool_exp_exp hole l) (cool_exp_exp hole r)
 | BNot e => BNot (cool_exp_exp hole e)
 | _ => froze
 end .

Definition cool_exp_stmt (hole : Exp) (froze : Stmt) :=
 match froze with
 | SAssign v e => SAssign v (cool_exp_exp hole e)
 | HAssign l r => HAssign (cool_exp_exp hole l) (cool_exp_exp hole r)
 | SIf e t l => SIf (cool_exp_exp hole e) t l
 | SWhile e b => SWhile (cool_exp_exp hole e) b
 | SReturn e => SReturn (cool_exp_exp hole e)
 | SCall f es => SCall f
     ((fix cool_exp_exps l :=
        match l with nil => nil
        | cons e es' => cons (cool_exp_exp hole e) (cool_exp_exps es')
        end) es)
 | _ => froze
 end.
Definition cool_exp_kitem (hole : Exp) (froze : kitem) : kitem :=
 match froze with
 | KStmt stmt => KStmt (cool_exp_stmt hole stmt)
 | KExp exp => KExp (cool_exp_exp hole exp)
 | _ => froze
 end.
(* TODO: lemmas that cooling behaves properly. *)

Fixpoint find_unevaluated_entry (exps : Map k k) :
  option (kitem * (Map k k)) :=
  match exps with
    | mapEmpty => None
    | mapItem k (kra v kdot) =>
      match KResultFromK v with
      | Some _ => None
      | None => Some (v, mapItem k (kra (KExp HOLE_Exp) kdot))
      end
    | mapItem _ _ => None
    | mapJoin l r =>
      match find_unevaluated_entry l with
        | Some (vl,kl) => Some (vl,mapJoin kl r)
        | None => match find_unevaluated_entry r with
                    | Some (vr,kr) => Some (vr,mapJoin l kr)
                    | None => None
                  end
      end
  end.

Function first_unevaluated_arg rbefore args :=
  match args with
    | nil => None
    | a :: args' =>
      match KResultFromExp a with
      | Some _ => first_unevaluated_arg (a::rbefore) args'
      | None => Some (ExpToK a, rev_append rbefore (HOLE_Exp :: args'))
      end
  end.

(* k completion-like notation *)
(*
Notation exp_step step a b :=
  (forall env stk henv lenv funs mark,
     step (KCfg a env stk henv lenv funs mark)
          (KCfg b env stk henv lenv funs mark)) (only parsing).

Notation exp1_step step a b := (forall rest, exp_step step (kra a rest) (kra b rest)) (only parsing).
*)

Inductive pat1 (A : Set) : Set :=
  | wild : pat1 A
  | read : A -> pat1 A
  | write : A -> A -> pat1 A.
Arguments wild {A}.
Definition arg (A : Set) (p : pat1 A) (k : A -> A -> Prop) : Prop :=
  match p with
    | wild => forall x, k x x
    | read x => k x x
    | write x1 x2 => k x1 x2
  end.

Inductive cell : Set :=
  | k_cell : pat1 k -> cell
  | env_cell : pat1 (Map k k) -> cell 
  | stk_cell : pat1 (list Frame) -> cell 
  | heap_cell : pat1 (Map k k) -> cell
  | fun_cell : pat1 (Map k k) -> cell
  .

Inductive pat : Set :=
  | KPat : pat1 k -> pat1 (Map k k) ->
           pat1 (list Frame) ->
           pat1 (Map k k) -> pat1 (Map k k) ->
           pat1 (Map k k) ->
    pat
  .

Definition ext (c : cell) (p : pat) : pat :=
  match p with
    | KPat k env stk heap code funs => 
      match c with
        | k_cell k => KPat k env stk heap code funs
        | env_cell env =>  KPat k env stk heap code funs
        | stk_cell stk =>  KPat k env stk heap code funs
        | heap_cell heap =>  KPat k env stk heap code funs
        | fun_cell funs =>  KPat k env stk heap code funs
      end
  end.


Definition mk_step (step : kcfg -> kcfg -> Prop) (p : pat) : Prop :=
  match p with
    | KPat k env stk heap code funs =>
      arg k (fun k1 k2 =>
      arg env (fun e1 e2 =>
      arg stk (fun s1 s2 =>
      arg heap (fun h1 h2 =>
      arg funs (fun f1 f2 =>
        step (KCfg k1 e1 s1 h1 f1) (KCfg k2 e2 s2 h2 f2))))))
  end.

Fixpoint mkpat (step : kcfg -> kcfg -> Prop) (p : pat)
   (members : list cell) : Prop :=
  match members with
    | nil => mk_step step p
    | c :: cells' => mkpat step (ext c p) cells'
  end.

Definition krule (step : kcfg -> kcfg -> Prop) (members : list cell) : Prop :=
  mkpat step (KPat wild wild wild wild wild wild) members.

Notation "'[' x ';' .. ';' y ']'" := (cons x (.. (cons y nil) ..)).

(*
Definition eval1 x y rest  := (k_cell (write (kra x rest)
                                           (kra y rest))).
Definition heat e h1 h2 rest := (k_cell (write (kra e rest)
                                               (kra h1 (kra h2 rest)))).
*)

(*
Definition heat_exp step e h1 h2 rest :=
  KResultFromExp h1 = None -> heat_step step e h1 h2 rest.

Notation heat_exp_1 step con :=
  (forall rest x, heat_exp step (con x) x (KFreeze con) rest).
Notation heat_exp_l step con :=
  (forall rest x y, heat_exp step (con x y) x (KFreeze (con HOLE_Exp y)) rest).
Notation heat_exp_r step con :=
  (forall rest x y, heat_exp step (con x y) y (KFreeze (con x HOLE_Exp)) rest).

Notation fun_rule step k1 k2 f1 f2 :=
  (forall env stk heap lenv mark,
    step (KCfg (kra k1 kdot) env stk heap lenv f1 mark)
         (KCfg (kra k2 kdot) env stk heap lenv f2 mark)).
*)

(*
Notation eval_rule step e1 e2 :=
  (forall rest, krule step [eval1 e1 e2 rest]).
 *)
Notation eval_rule step e1 e2 :=
  (forall rest, kcell_step step (kra e1 rest) (kra e2 rest)).

Definition stmt1 s rest  := (k_cell (write (kra s rest) rest)).
Definition stmt_step s1 s2 rest  := (k_cell (write (kra s1 rest) (kra s2 rest))).

Fixpoint all_values l :=
  match l with
  | nil => true
  | v :: l' =>
    match KResultFromExp v with
    | Some _ => all_values l'
    | None => false
    end
  end.

Fixpoint values exprs :=
  match exprs with
    | e :: exprs' =>
      match KResultFromExp e with
      | Some v => v :: values exprs'
      | None => nil
      end
    | _ => nil
  end.

Fixpoint is_value_map (m : Map k k) : bool :=
  match m with
    | mapItem k (kra v kdot) =>
      match KResultFromK v with
      | Some _ => true
      | None => false
      end
    | mapItem k _ => false
    | mapEmpty => true
    | mapJoin m1 m2 => andb (is_value_map m1) (is_value_map m2)
  end.


Fixpoint mkMap (formals : list string) (actuals : list Exp)
    : Map k k :=
  match formals, actuals with
    | f :: formals', a :: actuals' =>
        match KResultFromExp a with
        | Some v => kra (KId f) kdot |-> kra (KResultToK v) kdot
                 :* mkMap formals' actuals'
        | None => mapEmpty
        end
    | nil, nil => mapEmpty
    | _, _ => mapEmpty
  end.

Fixpoint replicate (n : nat) {A : Type} (a : A) : list A :=
  match n with
    | O => nil
    | S n' => a :: replicate n' a
  end.

Generalizable Variables rest env erest stk henv hrest lenv funs frest.


Definition notKResult (e : k) : bool :=
  match e with
    | kra item kdot =>
      match item with
        | KInt _ => false
        | KBool _ => false
        | KUndef _ => false
        | _ => true
      end
    | _ => true
  end.