Require Export himp_syntax.

(* Notations and coercions to make syntax nicer *)
Coercion EVar : string >-> Exp.
Coercion ECon : Z >-> Exp.
Coercion BCon : bool >-> Exp.
Coercion ExpToK : Exp >-> kitem.
Coercion KDefn : Defn >-> kitem.

Delimit Scope code with code.

Notation "{{ s1 ; .. ; sn }}" :=
  (Seq s1%code .. (Seq sn%code Skip) ..) (at level 5) : code.
Notation "t <- e" := (SAssign t e)
  (at level 100, e at level 200, no associativity) : code.
Notation "e1 <<- e2" := (HAssign e1 e2)
  (at level 100, e2 at level 200, no associativity) : code.
Infix "+" := EPlus : code.
Infix "=" := BEq : code.
Notation "x <> y" := (BNot (BEq (x : Exp) (y : Exp))) : code.
Infix "&&" := BAnd : code.
Infix "||" := BOr : code.
Notation "v ->> f" := (EProject (ELoad (v : Exp)) f)
  (at level 10, no associativity) : code.

Bind Scope code with Exp.
Bind Scope code with Stmt.

Arguments SWhile (c b)%code.
Arguments SIf (c t e)%code.
Arguments SReturn e%code.
Arguments FunDef name%string args%list body%code.
