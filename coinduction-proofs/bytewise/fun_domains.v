Require Import ZArith.
Require Import String.
Require Export maps.

Set Implicit Arguments.
Inductive float : Set :=.

Inductive Defn : Set :=
   FunDef : string -> list string -> Stmt -> Defn
with Exp : Set :=
   BCon : bool -> Exp
 | EVar : string -> Exp
 | ECon : Z -> Exp
 | ExpUndef : Undef -> Exp
 | ENeg : Exp -> Exp
 | EMult : Exp -> Exp -> Exp
 | EPlus : Exp -> Exp -> Exp
 | EMinus : Exp -> Exp -> Exp
 | EDiv : Exp -> Exp -> Exp
 | BLe : Exp -> Exp -> Exp
 | BLt : Exp -> Exp -> Exp
 | BEq : Exp -> Exp -> Exp
 | BAnd : Exp -> Exp -> Exp
 | BOr : Exp -> Exp -> Exp
 | EBuild : Map k k -> Exp
 | ECall : string -> list Exp -> Exp
 | ELoad : Exp -> Exp
 | BNot : Exp -> Exp
 | HOLE_Exp : Exp
with Frame : Set :=
   frame : k -> Map k k -> Frame
with kitem : Set :=
   KBool : bool -> kitem
 | KDefn : Defn -> kitem
 | KExp : Exp -> kitem
 | KExps : list Exp -> kitem
 | KFrame : Frame -> kitem
 | KFrames : list Frame -> kitem
 | KId : string -> kitem
 | KIds : list string -> kitem
 | KInt : Z -> kitem
 | KMap : Map k k -> kitem
 | KPgm : list Defn -> kitem
 | KStmt : Stmt -> kitem
 | KUndef : Undef -> kitem
 | KFreeze : kitem -> kitem
with KResult : Set :=
   Bool : bool -> KResult
 | Int : Z -> KResult
 | VUndef : Undef -> KResult
with Stmt : Set :=
   HAssign : Exp -> Exp -> Stmt
 | SAssign : string -> Exp -> Stmt
 | Seq : Stmt -> Stmt -> Stmt
 | Decl : string -> Stmt
 | SIf : Exp -> Stmt -> Stmt -> Stmt
 | Jump : Exp -> Stmt
 | SReturnVoid : Stmt
 | SReturn : Exp -> Stmt
 | SCall : string -> list Exp -> Stmt
 | Skip : Stmt
 | SWhile : Exp -> Stmt -> Stmt
with Undef : Set :=
   undef : Undef
with k : Set :=
   kdot : k
 | kra : kitem -> k -> k.

Definition KResultToExp (x : KResult) : Exp :=
  match x with
  | Bool i => BCon i
  | Int i => ECon i
  | VUndef i => ExpUndef i
  end.
Definition KResultFromExp (x : Exp) : option KResult :=
  match x with
  | BCon i => Some (Bool i)
  | ECon i => Some (Int i)
  | ExpUndef i => Some (VUndef i)
  | _ => None
  end.
Definition KResultToK (x : KResult) : kitem :=
  match x with
  | Bool i => KBool i
  | Int i => KInt i
  | VUndef i => KUndef i
  end.
Definition KResultFromK (x : kitem) : option KResult :=
  match x with
  | KBool i => Some (Bool i)
  | KInt i => Some (Int i)
  | KUndef i => Some (VUndef i)
  | _ => None
  end.
Definition ExpToK (x : Exp) : kitem :=
  match x with
  | BCon i => KBool i
  | EVar i => KId i
  | ECon i => KInt i
  | ExpUndef i => KUndef i
  | _ => KExp x
  end.
Definition ExpFromK (x : kitem) : option Exp :=
  match x with
  | KExp i => Some i
  | KBool i => Some (BCon i)
  | KId i => Some (EVar i)
  | KInt i => Some (ECon i)
  | KUndef i => Some (ExpUndef i)
  | _ => None
  end.
