Require Export maps.
Require Export ZArith.
Require Export List.

Open Scope list_scope.

Definition loc : Set := Z.
Inductive val : Set :=
 | Closure (body : exp) (context : env)
 | Num : nat -> val
 | Addr : loc -> val
 | Pair : val -> val -> val
 (* Primitive functions *)
 | Inc | Dec | Plus | Plus1 (x:nat)
 | Eq | Eq1 (a:val)
 | Nil | Cons | Cons1 (a:val) | Car | Cdr
with exp : Set :=
 | App (f x : exp)
 | Lit (v : val)
 | Var (ix : nat)
 | Lam (body : exp)
 | Closed (e : exp)
 | If (c t e : exp)
 | Seq (a b : exp)
 | Ref (e : exp) | Dealloc (v : exp)
 | Deref (e : exp) | Assign (v : exp) (e : exp)
with env : Set := Env : list val -> env.

Coercion App : exp >-> Funclass.
Coercion Lit : val >-> exp.

Definition Let := (Lam (Lam ((Var 0) (Var 1)))).
Definition strict_worker : exp := (Var 1)
  ((Closed (Lam (Lam (((Var 1) (Var 1)) (Var 0))))) (Var 0)).
Definition strict_fix : exp :=
  Closed (Lam ((Lam ((Var 0) (Var 0))) (Lam strict_worker))).

Local Ltac eq_assums := pose eq_nat_dec;pose Z_eq_dec;
   pose list_eq_dec;decide equality.
Fixpoint val_eq_dec (x y:val) : {x=y}+{x<>y}
with exp_eq_dec (x y:exp) : {x=y}+{x<>y}
with env_eq_dec (x y:env) : {x=y}+{x<>y}.
eq_assums. eq_assums. eq_assums.
Defined.

Inductive control : Set := Val (v : val)
                         | Exp (e : exp) (env : env).

Inductive cont : Set :=
    Top
  | AppFun (e' : exp) (scope : env) (k : cont) (* app fun [] e' *)
  | AppArg (v' : val) (k : cont)               (* app arg v' [] *)
  | RefVal (k : cont)                          (* ref [] *)
  | SeqCtx (e : exp) (scope : env) (k : cont)  (* [] ; e *)
  | DerefTgt (k : cont)                        (* ! [] *)
  | AssignTgt (e : exp) (scope : env) (k : cont) (* [] := e *)
  | AssignVal (l : loc) (k : cont)               (* l := [] *)
  | DeallocCtx (k : cont)                      (* dealloc [] *)
  | IfCond (t e : exp) (scope : env) (k : cont).

Inductive cfg : Set :=
  Cfg {code:control
      ;heap:Map loc val
      ;mark:loc
      ;ctx:cont}.

Fixpoint get (ix : nat) {A} (l : list A) : option A :=
  match ix, l with
    | _, nil => None
    | O, cons v _ => Some v
    | S ix', cons _ l' => get ix' l'
  end.
Definition getEnv (ix : nat) (p : env) :=
  match p with
    | Env l => get ix l
  end.
Definition extend (x : val) (p : env) : env :=
  match p with
    | Env l => Env (x :: l)
  end.

Definition apply (f : val) (v : val) : option control :=
  match f with
    | Closure e p' => Some (Exp e (extend v p'))
    | Inc => match v with
      | Num n => Some (Val (Num (S n)))
      | _ => None
      end
    | Dec => match v with
      | Num n => Some (Val (Num (pred n)))
      | _ => None
      end
    | Plus => match v with
      | Num n => Some (Val (Plus1 n))
      | _ => None
      end
    | Plus1 x => match v with
      | Num n => Some (Val (Num (x+n)))
      | _ => None
      end
    | Eq => Some (Val (Eq1 v))
    | Eq1 x => Some (if val_eq_dec x v then Val (Num 0)
                                       else Val Nil)
    | Cons => Some (Val (Cons1 v))
    | Cons1 a => Some (Val (Pair a v))
    | Car => 
      match v with
        | Pair a _ => Some (Val a)
        | _ => None
      end
    | Cdr =>
      match v with
        | Pair _ b => Some (Val b)
        | _ => None
      end
    | Pair _ _ => None
    | Nil => None
    | Num _ => None
    | Addr _ => None
  end.

Definition isNil v :=
  match v with
    | Nil => true
    | _ => false
  end.

Inductive lam_step : cfg -> cfg -> Prop :=
  | enter_function : forall e0 e1 p s m k,
      lam_step (Cfg (Exp (App e0 e1) p) s m k)
               (Cfg (Exp e0 p)          s m (AppFun e1 p k))
  | enter_argrgument : forall v s e p m k,
      lam_step (Cfg (Val v)   s m (AppFun e p k))
               (Cfg (Exp e p) s m (AppArg v k))
  | eval_call : forall v s f k m r, apply f v = Some r ->
       lam_step (Cfg (Val v) s m (AppArg f k))
                (Cfg r       s m k)
  | eval_lit : forall v p s m k,
      lam_step (Cfg (Exp (Lit v) p) s m k)
               (Cfg (Val v)         s m k)
  | eval_lam : forall e p s m k,
      lam_step (Cfg (Exp (Lam e) p)     s m k)
               (Cfg (Val (Closure e p)) s m k)
  | eval_var : forall i p v s m k, get i p = Some v ->
      lam_step (Cfg (Exp (Var i) (Env p)) s m k)
               (Cfg (Val v)               s m k)
  | enter_seq : forall e e' p s m k,
      lam_step (Cfg (Exp (Seq e e') p) s m k)
               (Cfg (Exp e p)          s m (SeqCtx e' p k))
  | eval_seq : forall v e p s m k,
      lam_step (Cfg (Val v)   s m (SeqCtx e p k))
               (Cfg (Exp e p) s m k)
  | enter_if : forall c t e p s m k,
      lam_step (Cfg (Exp (If c t e) p) s m k)
               (Cfg (Exp c p)          s m (IfCond t e p k))
  | eval_if_nil : forall v s t e p m k, isNil v = true ->
      lam_step (Cfg (Val v)   s m (IfCond t e p k))
               (Cfg (Exp e p) s m k)
  | eval_if_nonnil : forall v s t e p m k, isNil v = false ->
      lam_step (Cfg (Val v)   s m (IfCond t e p k))
               (Cfg (Exp t p) s m k)
  | enter_ref : forall e p s m k,
      lam_step (Cfg (Exp (Ref e) p) s m k)
               (Cfg (Exp e p)       s m (RefVal k))
  | eval_ref : forall v s m k,
      lam_step (Cfg (Val v)         s            m   (RefVal k))
               (Cfg (Val (Addr m)) (m|->v :* s) (m+1) k)%Z
  | enter_dealloc : forall e p s m k,
      lam_step (Cfg (Exp (Dealloc e) p) s m k)
               (Cfg (Exp e p)           s m (DeallocCtx k))
  | eval_dealloc : forall l s x s' m k, s ~= l|->x :* s' ->
      lam_step (Cfg (Val (Addr l)) s  m (DeallocCtx k))
               (Cfg (Val Nil)      s' m k)
  | enter_deref : forall e p s m k,
      lam_step (Cfg (Exp (Deref e) p) s m k)
               (Cfg (Exp e p)         s m (DerefTgt k))
  | eval_deref : forall l v s s' m k, s ~= l|->v :* s' ->
      lam_step (Cfg (Val (Addr l)) s m (DerefTgt k))
               (Cfg (Val v)        s m k)
  | enter_assign_target : forall t e p s m k,
      lam_step (Cfg (Exp (Assign t e) p) s m k)
               (Cfg (Exp t p)            s m (AssignTgt e p k))
  | enter_assign_val : forall l p e' s m k,
      lam_step (Cfg (Val (Addr l)) s m (AssignTgt e' p k))
               (Cfg (Exp e' p)     s m (AssignVal l k))
  | eval_assign : forall l v s w s' m k, s ~= l|->w :* s' ->
      lam_step (Cfg (Val v) s             m(AssignVal l k))
               (Cfg (Val v) (l|->v :* s') m k)
  | close_exp : forall e v s m k,
      lam_step (Cfg (Exp (Closed e) v)        s m k)
               (Cfg (Exp  e        (Env nil)) s m k).
