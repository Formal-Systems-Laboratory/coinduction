Require Import String.
Require Import ZArith.
Require Import fun_domains.

Notation "x 's|->' y" := (mapItem (kra (KId x) kdot) (kra (y : kitem) kdot))
  (at level 50, no associativity) : Map.
Notation funEntry name args body :=
   (name%string s|-> FunDef name args body).

(* Notations and coercions to make syntax nicer *)
Coercion EVar : string >-> Exp.
Coercion ECon : Z >-> Exp.
Coercion BCon : bool >-> Exp.
Coercion ExpToK : Exp >-> kitem.
Coercion KDefn : Defn >-> kitem.

Delimit Scope code with code.

Notation "{{ s1 ; .. ; sn }}" := (Seq s1%code .. (Seq sn%code Skip) ..) (at level 5) : code.
Notation "t <- e" := (SAssign t e) (at level 100, e at level 200, no associativity) : code.
Notation "e1 <<- e2" := (HAssign e1 e2) (at level 100, e2 at level 200, no associativity) : code.
Infix "+" := EPlus : code.
Infix "=" := BEq : code.
Notation "x <> y" := (BNot (BEq (x : Exp) (y : Exp))) : code.
Infix "&&" := BAnd : code.
Infix "||" := BOr : code.

Bind Scope code with Exp.
Bind Scope code with Stmt.

Arguments SWhile (c b)%code.
Arguments SIf (c t e)%code.

Open Scope Z_scope.