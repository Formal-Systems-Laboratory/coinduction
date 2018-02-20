Require Import ZArith.
Require Import String.
Require Import List.

Require Import sets.
Require Export imp_domains.

Set Implicit Arguments.

Notation "'[' x ';' .. ';' y ']'" := (cons x (.. (cons y nil) ..)).

Inductive pat1 (A : Set) : Set :=
  | wild : pat1 A
  | read : A -> pat1 A
  | write : A -> A -> pat1 A.
Arguments wild {A}.
Definition arg (A : Set) (p : pat1 A) (k : A -> A -> Prop) : Prop :=
  match p with
    | wild => forall {x}, k x x
    | read x => k x x
    | write x1 x2 => k x1 x2
  end.

Record kcfg := KCfg { kcell : k; state : Map k k }.

Inductive cell : Set :=
  | k_cell : pat1 k -> cell
  | state_cell : pat1 (Map k k) -> cell
  .
Inductive pat : Set :=
  | KPat : pat1 k -> pat1 (Map k k) -> pat
  .
Definition ext (c : cell) (p : pat) : pat :=
  match p with
    | KPat k state =>
      match c with
        | k_cell k => KPat k state
        | state_cell state =>  KPat k state
      end
  end.

Definition mk_step (step : kcfg -> kcfg -> Prop) (p : pat) : Prop :=
  match p with
    | KPat k state =>
      arg k (fun k1 k2 =>
      arg state (fun e1 e2 =>
        step (KCfg k1 e1) (KCfg k2 e2)))
  end.

Fixpoint mkpat (step : kcfg -> kcfg -> Prop) (p : pat)
   (members : list cell) : Prop :=
  match members with
    | nil => mk_step step p
    | c :: cells' => mkpat step (ext c p) cells'
  end.
Definition krule (step : kcfg -> kcfg -> Prop) (members : list cell) : Prop :=
  mkpat step (KPat wild wild) members.

Definition string_eqb (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

Definition kitem_equal (x y : kitem) : bool :=
  match x, y with
  | k_wrap_zhBool_KItem a, k_wrap_zhBool_KItem b =>
      Bool.eqb a b
  | k_wrap_zhInt_KItem a, k_wrap_zhInt_KItem b =>
      Z.eqb a b
  | k_wrap_Id_KItem (k_token_Id a), k_wrap_Id_KItem (k_token_Id b) =>
      string_eqb a b
  | _, _ =>
      false
  end.

Fixpoint k_equal (x y : k) : bool :=
  match x, y with
  | kdot, kdot => true
  | kra i1 x', kra i2 y' => andb (kitem_equal i1 i2) (k_equal x' y')
  | _, _ => false
  end.

Definition (* '_=/=K_ *) k_label_zqzuzezszeKzu (x y : k) : Bool :=
  k_wrap_zhBool_Bool (negb (k_equal x y)).

Definition k_label_isKResult (k : kitem) : Bool :=
  k_wrap_zhBool_Bool
  match k_proj_KResult_KItem k with
  | Some _ => true
  | None => false
  end.

Definition (* 'notBool_ *) k_label_zqnotBoolzu (b : Bool) : Bool :=
  match b with
  | k_wrap_zhBool_Bool b => k_wrap_zhBool_Bool (negb b)
  | _ => b
  end.
Definition (* '_+Int_ *) k_label_zqzuzpIntzu (x y : Int) : Int :=
  match x, y with
  | k_wrap_zhInt_Int a, k_wrap_zhInt_Int b => k_wrap_zhInt_Int (a + b)
  end.
Definition (* '_-Int_ *) k_label_zqzuzsIntzu (x y : Int) : Int :=
  match x, y with
  | k_wrap_zhInt_Int a, k_wrap_zhInt_Int b => k_wrap_zhInt_Int (a - b)
  end.
Definition (* '_==Int_ *) k_label_zqzuzezszeIntzu (x y : Int) : Bool :=
  match x, y with
  | k_wrap_zhInt_Int a, k_wrap_zhInt_Int b => k_wrap_zhBool_Bool (Z.eqb a b)
  end.
Definition (* '_<=Int_ *) k_label_zqzuzlzeIntzu (x y : Int) : Bool :=
  match x, y with
  | k_wrap_zhInt_Int a, k_wrap_zhInt_Int b => k_wrap_zhBool_Bool (Z.leb a b)
  end.

Definition (* 'keys *) k_label_zqkeys (m : Map k k) : MultiSet k := keys m.

Fixpoint inSetb (v : k) (s : MultiSet k) : bool :=
  match s with
  | setEmpty => false
  | setItem v' => k_equal v v'
  | setJoin l r => orb (inSetb v l) (inSetb v r)
  end.

Definition (* '_in_ *) k_label_zqzuinzu (v : k) (s : MultiSet k) : Bool :=
 k_wrap_zhBool_Bool (inSetb v s).
