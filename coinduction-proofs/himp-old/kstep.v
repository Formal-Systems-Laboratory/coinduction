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

Notation FreezeL f e := (KFreezeE (fun x => f x e)).
Notation FreezeR f e := (KFreezeE (fun x => f e x)).

Notation "'□' '+' e" := (FreezeL EPlus e) (at level 50) : k_scope.
Notation "e '+' '□'" := (FreezeR EPlus e) (at level 50) : k_scope.
Notation "'□' '-' e" := (FreezeL EMinus e) (at level 50) : k_scope.
Notation "e '-' '□'" := (FreezeR EMinus e) (at level 50) : k_scope.
Notation "'□/' e" := (FreezeL EDiv e) (at level 50): k_scope.
Notation "e '/□'" := (FreezeR EDiv e) (at level 50): k_scope.
Notation "'□<=' e" := (FreezeL BLe e) (at level 70): k_scope.
Notation "i '<=□'" := (FreezeR BLe (ECon i)) (at level 70): k_scope.
Notation "'□==' e" := (FreezeL BEq e) (at level 70): k_scope.
Notation "i '==□'" := (FreezeR BEq (ECon i)) (at level 70): k_scope.
Notation "'□&&' e" := (KFreezeB (fun l => BAnd l e)) (at level 50): k_scope.
Notation "v ':=□'" := (KFreezeE (fun e => SAssign v e)) (at level 70): k_scope.
Notation "'if□then' s1 'else' s2" := (KFreezeB (fun b => SIf b s1 s2)) (at level 20): k_scope.

Delimit Scope k_scope with K.
Open Scope k_scope.

Coercion KExp : Exp >-> kitem.
Coercion KBExp : BExp >-> kitem.
Coercion KStmt : Stmt >-> kitem.

Set Implicit Arguments.

Notation exp_step step a b :=
  (forall env henv lenv,
     step (KCfg a env henv lenv)
          (KCfg b env henv lenv)) (only parsing).

Notation exp1_step step a b := (forall rest, exp_step step (kra a rest) (kra b rest)) (only parsing).

Notation heat_step step cool hot ctx :=
  (forall rest, exp_step step (kra cool rest) (kra hot (kra ctx rest))).
Notation cool_step step hot ctx cool :=
  (forall rest, exp_step step (kra hot (kra ctx rest)) (kra cool rest)).

Generalizable Variables rest env erest henv hrest lenv x y i j v r e b s.
Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  | k_amb_left : `(kstep (KCfg (kra (EAmb x y) rest) env henv lenv)
                         (KCfg (kra x rest) env henv lenv))
  | k_amb_right : `(kstep (KCfg (kra (EAmb x y) rest) env henv lenv)
                          (KCfg (kra y rest) env henv lenv))
  | k_lookup : `(env ~= (x |-> i :* erest) ->
                 kstep (KCfg (kra (EVar x) rest) env henv lenv)
                       (KCfg (kra (ECon i) rest) (x |-> i :* erest) henv lenv))
  | k_load : `(henv ~= (i |-> j :* hrest) ->
                 kstep (KCfg (kra (ELoad (ECon i)) rest) env henv lenv)
                       (KCfg (kra (ECon j) rest) env henv lenv))
  | k_assign : `(env ~= (x |-> v :* erest) ->
                 kstep (KCfg (kra (SAssign x (ECon i)) rest) env henv lenv)
                       (KCfg             rest (x |-> i :* erest) henv lenv))
  | k_hassign : `(henv ~= (i |-> v :* hrest) ->
                 kstep (KCfg (kra (HAssign (ECon i) (ECon j)) rest) env henv lenv)
                       (KCfg                     rest env (i |-> j :* hrest) lenv))
  | k_jump : `(forall l,
                 lenv ~= (l |-> s :* erest) ->
                 kstep (KCfg (kra (Jump (ECon l)) rest) env henv lenv)
                       (KCfg (kra s kdot) env henv lenv))
  | k_plus : `(exp1_step kstep (EPlus (ECon i) (ECon j))
                               (ECon (Zplus i j)))
  | k_minus : `(exp1_step kstep (EMinus (ECon i) (ECon j))
                                (ECon (Zminus i j)))
  | k_div : `(Zneq_bool 0%Z j = true ->
               exp1_step kstep (EDiv (ECon i) (ECon j))
                               (ECon (Zdiv i j)))
  | k_le : `(exp1_step kstep (BLe (ECon i) (ECon j))
                             (BCon (Zle_bool i j)))
  | k_eq : `(exp1_step kstep (BEq (ECon i) (ECon j))
                             (BCon (i =? j)%Z))
  | k_not : `(exp1_step kstep (BNot (BCon b)) (BCon (negb b)))
  | k_and_t : `(exp1_step kstep (BAnd (BCon true) b)
                                b)
  | k_and_f : `(exp1_step kstep (BAnd (BCon false) b)
                                (BCon false))
  | k_skip: `(exp_step kstep (kra Skip rest)
                             rest)
  | k_if_t : `(exp1_step kstep (SIf (BCon true) s1 s2)
                               s1)
  | k_if_f : `(exp1_step kstep (SIf (BCon false) s1 s2)
                         s2)
  | k_while : `(exp1_step kstep (SWhile b s)
                                (SIf b (Seq s (SWhile b s)) Skip))
  (* heating and cooling *)
  | k_cool_e : `(cool_step kstep (ECon i) (KFreezeE e) (e (ECon i)))
  | k_cool_b : `(cool_step kstep (BCon b) (KFreezeB e) (e (BCon b)))
  (* unary *)
  | k_heat_load : `(isEVal e = false -> heat_step kstep (ELoad e) e (KFreezeE ELoad))
  (* plus *)
  | k_heat_plus_l : `(isEVal e = false ->  heat_step kstep (EPlus e e2) e  (□ + e2))
  | k_heat_plus_r : `(isEVal e2 = false -> heat_step kstep (EPlus e e2) e2 (e + □))
  (* minus *)
  | k_heat_minus_l : `(isEVal e = false ->  heat_step kstep (EMinus e e2) e  (□ - e2))
  | k_heat_minus_r : `(isEVal e2 = false -> heat_step kstep (EMinus e e2) e2 (e - □))
  (* div *)
  | k_heat_div_l : `(isEVal e = false ->  heat_step kstep (EDiv e e2) e (□/ e2))
  | k_heat_div_r : `(isEVal e2 = false -> heat_step kstep (EDiv e e2) e2 (e /□))
  (* le is seqstrict *)
  | k_heat_le_l : `(isEVal e = false ->  heat_step kstep (BLe e e2) e (□<= e2))
  | k_heat_le_r : `(isEVal e2 = false -> heat_step kstep (BLe (ECon i) e2) e2 (i <=□))
  (* eq is seqstrict *)
  | k_heat_eq_l : `(isEVal e = false ->  heat_step kstep (BEq e e2) e (□== e2))
  | k_heat_eq_r : `(isEVal e2 = false -> heat_step kstep (BEq (ECon i) e2) e2 (i ==□))
  (* and is only strict in left argument *)
  | k_heat_not : `(isBool b = false -> heat_step kstep (BNot b) b (KFreezeB BNot))
  | k_heat_and : `(isBool b1 = false -> heat_step kstep (BAnd b1 b2) b1 (□&& b2))
  (* assign *)
  | k_heat_assign : `(isEVal e = false -> heat_step kstep (SAssign x e) e (x :=□))
  (* hassign *)
  | k_heat_hassign_l : `(isEVal e  = false -> heat_step kstep (HAssign e e2) e  (FreezeL HAssign e2))
  | k_heat_hassign_r : `(isEVal e2 = false -> heat_step kstep (HAssign e e2) e2 (FreezeR HAssign e))
  (* jump *)
  | k_heat_jump : `(isEVal e = false -> heat_step kstep (Jump e) e (KFreezeE Jump))
  (* if *)
  | k_heat_if : `(isBool b = false -> heat_step kstep (SIf b s1 s2) b (if□then s1 else s2))
  (* seq *)
  | k_heat_seq : `(heat_step kstep (Seq s1 s2) s1 s2)
  .
