Require Export ZArith.
Require Export String.
Require Export List.
Require Export maps.

Global Open Scope Z_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.

Set Implicit Arguments.

Inductive Defn : Set :=
   FunDef : string -> list string -> Stmt -> Defn
with Exp : Set :=
   BCon : bool -> Exp
 | EVar : string -> Exp
 | ECon : Z -> Exp
 | EValStruct : sval -> Exp
 | ExpUndef : Undef -> Exp
 | ENeg : Exp -> Exp
 | EMult : Exp -> Exp -> Exp
 | EPlus : Exp -> Exp -> Exp
 | EMinus : Exp -> Exp -> Exp
 | EProject : Exp -> string -> Exp
 | EDiv : Exp -> Exp -> Exp
 | BLe : Exp -> Exp -> Exp
 | BLt : Exp -> Exp -> Exp
 | BEq : Exp -> Exp -> Exp
 | BAnd : Exp -> Exp -> Exp
 | BOr : Exp -> Exp -> Exp
 | EAlloc : Exp
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
 | KStruct : sval -> kitem
 | KUndef : Undef -> kitem
 | KFreeze : kitem -> kitem
with KResult : Set :=
   Bool : bool -> KResult
 | Int : Z -> KResult
 | VStruct : sval -> KResult
 | VUndef : Undef -> KResult
with Stmt : Set :=
   HAssign : Exp -> Exp -> Stmt
 | SAssign : string -> Exp -> Stmt
 | Seq : Stmt -> Stmt -> Stmt
 | HDealloc : Exp -> Stmt
 | Decl : string -> Stmt
 | SIf : Exp -> Stmt -> Stmt -> Stmt
 | Jump : Exp -> Stmt
 | SReturnVoid : Stmt
 | SReturn : Exp -> Stmt
 | SCall : string -> list Exp -> Stmt
 | Skip : Stmt
 | SWhile : Exp -> Stmt -> Stmt
with sval : Set :=
   Struct : Map k k -> sval
with Undef : Set :=
   undef : Undef
with k : Set := kdot | kra : kitem -> k -> k
 .

Definition KResultToExp (x : KResult) : Exp :=
  match x with
  | Bool i => BCon i
  | Int i => ECon i
  | VStruct i => EValStruct i
  | VUndef i => ExpUndef i
  end.
Definition KResultFromExp (x : Exp) : option KResult :=
  match x with
  | BCon i => Some (Bool i)
  | ECon i => Some (Int i)
  | EValStruct i => Some (VStruct i)
  | ExpUndef i => Some (VUndef i)
  | _ => None
  end.
Definition KResultToK (x : KResult) : kitem :=
  match x with
  | Bool i => KBool i
  | Int i => KInt i
  | VStruct i => KStruct i
  | VUndef i => KUndef i
  end.
Definition KResultFromK (x : kitem) : option KResult :=
  match x with
  | KBool i => Some (Bool i)
  | KInt i => Some (Int i)
  | KStruct i => Some (VStruct i)
  | KUndef i => Some (VUndef i)
  | _ => None
  end.
Definition ExpToK (x : Exp) : kitem :=
  match x with
  | BCon i => KBool i
  | EVar i => KId i
  | ECon i => KInt i
  | EValStruct i => KStruct i
  | ExpUndef i => KUndef i
  | _ => KExp x
  end.
Definition ExpFromK (x : kitem) : option Exp :=
  match x with
  | KBool i => Some (BCon i)
  | KExp i => Some i
  | KId i => Some (EVar i)
  | KInt i => Some (ECon i)
  | KStruct i => Some (EValStruct i)
  | KUndef i => Some (ExpUndef i)
  | _ => None
  end.