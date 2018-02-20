Require Import String.

(* A more basic CEK machine, leaving out the heap,
   pairs, and most arithmetic operations compared to the main lambda *)

Inductive value : Set := Lam (body : exp)
  | Neutral : string -> list (value * env) -> value
  | Num : nat -> value
  | Inc : value
with exp : Set := App (f x : exp) | Var (ix : nat) | Val (v : value)
with env : Set := Env : list (value * env) -> env.

Coercion Val : value >-> exp.

Inductive cont : Set :=
    Top
  | Arg (e' : exp) (scope : env) (k : cont)
  | Fun (v' : value) (scope : env) (k : cont)
  .

Fixpoint get (ix : nat) {A} (l : list A) : option A :=
  match ix, l with
    | _, nil => None
    | O, cons v _ => Some v
    | S ix', cons _ l' => get ix' l'
  end.

Definition extend (x : value * env) (p : env) : env :=
  match p with
    | Env l => Env (x :: l)
  end.
Inductive cfg : Set := Cfg : exp -> env -> cont -> cfg.

Definition apply (f : value) (p' : env) (v : value) (p : env) : option (exp * env) :=
  match f with
    | Lam e => Some (e, extend (v,p) p')
    | Neutral head args => Some (Val (Neutral head (app args ((v,p)::nil))), p')
    | Num n => None
    | Inc => match v with
      | Num n => Some (Val (Num (S n)), p')
      | _ => None
      end
  end.

Definition step' (c : cfg) : option cfg :=
  match c with
    | Cfg (Var i) (Env p) k =>
      match get i p with
        | Some (v,p') => Some (Cfg v p' k)
        | None => None
      end
    | Cfg (App e0 e1) p k => Some (Cfg e0 p (Arg e1 p k))
    | Cfg (Val v) p (Arg e p' k) => Some (Cfg e p' (Fun v p k))
    | Cfg (Val v) p (Fun f p' k) =>
      match apply f p' v p with
      | Some (e,p'') => Some (Cfg e p'' k)
      | None => None
      end
    | Cfg (Val v) _ Top => None
    end.
Functional Scheme step'_ind := Induction for step' Sort Prop.

Inductive step : cfg -> cfg -> Prop :=
  | lookup : forall i p v p' k,
      get i p = Some (v, p') -> step (Cfg (Var i) (Env p) k) (Cfg v p' k)
  | function : forall e0 e1 p k,
      step (Cfg (App e0 e1) p k) (Cfg e0 p (Arg e1 p k))
  | argrgument : forall v p e p' k,
      step (Cfg (Val v) p (Arg e p' k)) (Cfg e p' (Fun v p k))
  | call : forall v p f p' e p'' k,
       apply f p' v p = Some (e,p'') ->
       step (Cfg (Val v) p (Fun f p' k)) (Cfg e p'' k)
  .

Lemma stepdefs :
  forall st st', step st st' <-> step' st = Some st'.
split.
destruct 1;simpl;try rewrite H;reflexivity.
functional induction (step' st);
(discriminate 1 || injection 1;clear H;intro;subst);
constructor(assumption).
Qed.
  
(*
  | apply_lam : forall v p e p' k,
      step (Cfg (Val v) p (Fun (Lam e) p' k)) (Cfg e (extend (v,p) p') k)
  | apply_n : forall v p head args p' k,
      step (Cfg (Val v) p (Fun (Neutral head args) p' k))
           (Cfg (Neutral head (app args ((v,p)::nil))) p' k)
  .
 *)

Inductive goes {A} (rel : A -> A -> Prop) (cfg : A) : Prop :=
  | Step : forall cfg', rel cfg cfg' -> goes rel cfg' -> goes rel cfg
  | Done : goes rel cfg.

Definition init (e : exp) : cfg := Cfg e (Env nil) Top.

Definition church (n : nat) : exp :=
  let body := fix body n : exp := match n with
    | O => Var 0
    | S n' => App (Var 1) (body n')
    end
  in Lam (Lam (body n)).

Definition church_plus :=
  Lam (Lam (Lam (Lam (App (App (Var 3) (Var 1)) (App (App (Var 2) (Var 1)) (Var 0)))))).

Goal (goes step (init
     (App (App (App (App church_plus (church 2)) (church 3)) Inc)
       (Num 0)))).
cbv [init].
Ltac tick := eapply Step;[solve[constructor(reflexivity)]|];instantiate;cbv[extend app].
repeat tick.
apply Done.
Qed.
