Require Import lambda.
Require Import maps.
Require Import ZArith.

Open Scope list.

(* assume the existence of some map operations *)

(* add an entry, requiring it to be free *)
Axiom alloc : forall {A}, loc -> A -> Map loc A -> option (Map loc A).
(* remove a binding, requiring it to exist *)
Axiom free : forall {A}, loc -> Map loc A -> option (Map loc A).
(* update an existing binding *)
Axiom poke : forall {A}, loc -> A -> Map loc A -> option (Map loc A).
(* lookup the value of a binding *)
Axiom peek : forall {A}, loc -> Map loc A -> option A.

(* Attempt to make an evaluation function *)
Definition lam_step' (c : cfg) : option cfg :=
  match c with
    | Cfg (Exp e p) s m k =>
      match e with
        | Lit v => Some (Cfg (Val v) s m k)
        | Seq e e' => Some (Cfg (Exp e p) s m (SeqCtx e' p k))
        | Lam body => Some (Cfg (Val (Closure body p)) s m k)
        | Var i =>
          match p with
            | Env l =>
              match get i l with
                | Some v => Some (Cfg (Val v) s m k)
                | None => None
              end
          end
        | App e0 e1 => Some (Cfg (Exp e0 p) s m (AppFun e1 p k))
        | Ref e => Some (Cfg (Exp e p) s m (RefVal k))
        | Dealloc e => Some (Cfg (Exp e p) s m (DeallocCtx k))
        | Deref e => Some (Cfg (Exp e p) s m (DerefTgt k))
        | Assign e e' => Some (Cfg (Exp e p) s m (AssignTgt e' p k))
        | If ec t e => Some (Cfg (Exp ec p) s m (IfCond t e p k))
        | Closed e => Some (Cfg (Exp e (Env nil)) s m k)
      end
    | Cfg (Val v) s m k =>
      match k with
        | Top => None
        | AppFun e p k => Some (Cfg (Exp e p) s m (AppArg v k))
        | AppArg f k =>
          match apply f v with
            | Some c => Some (Cfg c s m k)
            | _ => None
          end
        | SeqCtx e p k =>
          Some (Cfg (Exp e p) s m k)
        | RefVal k =>
            match alloc m v s with
            | Some s' => Some (Cfg (Val (Addr m)) s' (m+1)%Z k)
            | None => None
            end
        | DerefTgt k =>
          match v with
            | Addr l =>
              match peek l s with
                | Some v => Some (Cfg (Val v) s m k)
                | _ => None
              end
            | _ => None
          end
        | AssignTgt e p k =>
          match v with
            | Addr l => Some (Cfg (Exp e p) s m (AssignVal l k))
            | _ => None
          end
        | AssignVal l k =>
          match poke l v s with
            | Some s' => Some (Cfg (Val v) s' m k)
            | None => None
          end
        | DeallocCtx k =>
          match v with
            | Addr l =>
              match free l s with
                | Some s' => Some (Cfg (Val Nil) s' m k)
                | None => None
              end
            | _ => None
          end
        | IfCond t e p k =>
          Some (Cfg (Exp (if isNil v then e else t) p) s m k)
      end
  end.
Functional Scheme lam_step'_ind := Induction for lam_step' Sort Prop.

Ltac inject1 :=
  let H := fresh in intro H; injection H; clear H;intro;subst.
Lemma func_valid : forall st st',
  lam_step' st = Some st' -> lam_step st st'.
intros st st';functional induction (lam_step' st);(discriminate 1 || inject1);
try solve[constructor(assumption)].
(* the remaining four clauses use the axiomatized map operations *)
admit.
admit.
admit.
admit.
Qed.

(* This one actually needs some kind of well-formedness assumption on the map,
   to ensure the deterministic peek/poke result agrees with
   the pattern-based statement *)
Lemma func_complete : forall st st',
   lam_step st st' -> lam_step' st = Some st'.
destruct 1;simpl; try match goal with
| [H : ?l = _ |- _] => rewrite H
end;try reflexivity.
admit.
admit.
admit.
admit.
Qed.