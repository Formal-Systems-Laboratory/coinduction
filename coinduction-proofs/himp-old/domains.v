Require Import BinPos.
Require Import ZArith.
Require Import FMapPositive.
Require Import String.

Require Import Setoid.

Require Export maps.

Set Implicit Arguments.

(* Syntax *)
Inductive Exp :=
  | EVar (v:string)
  | ELoad (x : Exp)
  | ECon (i:Z)
  | EPlus (l r:Exp)
  | EMinus (l r:Exp)
  | EDiv (l r:Exp)
  | EAmb (x y : Exp)
  .
Definition isEVal e :=
  match e with
    | ECon _ => true
    | _ => false
  end.

Inductive BExp :=
  | BCon (b:bool)
  | BLe (l r : Exp)
  | BEq (l r : Exp)
  | BNot (e:BExp)
  | BAnd (l r:BExp)
  .
Definition isBool b :=
  match b with
    | BCon _ => true
    | _ => false
  end.
Inductive Stmt :=
  | Skip
  | SAssign (x:string) (e:Exp)
  | HAssign (e:Exp) (e2:Exp)
  | Seq (s1 s2 : Stmt)
  | SIf (b:BExp) (sthn sels : Stmt)
  | SWhile (b:BExp) (body:Stmt)
  | Jump (e : Exp)
  .

(* Assemble K type *)
Inductive kitem : Set :=
  | KExp (e : Exp)
  | KBExp (b : BExp)
  | KStmt (s : Stmt)
  | KFreezeE (f : Exp -> kitem)
  | KFreezeB (f : BExp -> kitem)
  .

Definition kra : kitem -> list kitem -> list kitem := @cons kitem.
Definition kdot : list kitem := nil.

(* Configuration *)

Structure kcfg := KCfg {
  kcell : list kitem;
  store : Map string Z;
  heap : Map Z Z;
  labels : Map Z Stmt
  }.

