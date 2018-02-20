Require Import lambda.

Require Import maps.
Require Import proof.
Require Import ZArith.

(* Various hardcoded examples checking that the
   semantics lets some simple programs evaluate properly *)

Definition init exp := Cfg (Exp exp (Env nil)) mapEmpty 1%Z Top.
Definition finished c :=
  match c with
    | Cfg (Val _) _ _ Top => True
    | _ => False
  end.

Definition church (n : nat) : exp :=
  let body := fix body n : exp := match n with
    | O => Var 0
    | S n' => App (Var 1) (body n')
    end
  in Lam (Lam (body n)).

Coercion Var : nat >-> exp.

Definition church_plus := Lam (Lam (Lam (Lam ((3 1) ((2 1) 0))))).

Ltac tick :=
  eapply rstep;[solve[econstructor(reflexivity || equate_maps)]|];
   instantiate;cbv[extend].

Goal (reaches lam_step 
       (init ((church_plus (church 2) (church 3)) Inc (Num 0)))
       (eq (Cfg (Val (Num 5)) mapEmpty 1%Z Top))).
cbv [init].
repeat tick.
eapply rdone. reflexivity.
Qed.

(* \f . (\v . v v) (\v . f (\x . ((v v) x))) *)
Definition strict_fix : exp := Lam ((Lam (0 0) (Lam (1 (Lam ((1 1) 0)))))).

Definition plus : exp :=
  strict_fix (Lam (Lam (Lam (If (Eq (Num 0) 1) 0 (Inc (2 (Dec 1) 0)))))).

Goal (reaches lam_step (init (plus (Num 2) (Num 2)))
     (eq (Cfg (Val (Num 4)) mapEmpty 1%Z Top))).
repeat tick.
eapply rdone.
reflexivity.
Qed.

Definition Let e e' := (Lam e') e.

(* A list is Nil, or an address holding a pair of
   a value and the tail of the list *)

Definition list_app_nonempty :=
  strict_fix (Lam (Lam
    (Let (Deref 0) (If (Cdr 0) (2 (Cdr 0)) (Assign 1 (Cons (Car 0) 3)))))).
Definition list_app := (Lam (Lam (If 1 (Seq (list_app_nonempty 1) 1) 0))).

Goal (reaches lam_step (Cfg (Exp (list_app (Addr 0) (Addr 3)) (Env nil))
                     (0 |-> Pair (Num 0) (Addr 1)
                     :* 1 |-> Pair (Num 1) Nil
                     :* 3 |-> Pair (Num 2) Nil)
                     1
                     Top)
                     (eq (Cfg (Val (Addr 0))
                     (1 |-> Pair (Num 1) (Addr 3)
                     :* 0 |-> Pair (Num 0) (Addr 1)
                     :* 3 |-> Pair (Num 2) Nil)
                     1
                     Top)))%Z.
cbv [init].
repeat tick.
apply rdone.
reflexivity.
Qed.

Goal (reaches lam_step (Cfg (Exp (list_app Nil (Addr 3)) (Env nil))
                     (0 |-> Pair (Num 0) (Addr 1)
                     :* 1 |-> Pair (Num 1) Nil
                     :* 3 |-> Pair (Num 2) Nil)
                     1
                     Top)
                     (eq (Cfg (Val (Addr 3))
                     (0 |-> Pair (Num 0) (Addr 1)
                     :* 1 |-> Pair (Num 1) Nil
                     :* 3 |-> Pair (Num 2) Nil)
                     1
                     Top)))%Z.
cbv [init].
repeat tick.
apply rdone.
reflexivity.
Qed.

Definition list_rev_app :=
  strict_fix (Lam (Lam (Lam (If 1
    (Let (Deref 1)
     (Seq (Assign 2 (Cons (Car 0) 1))
          (3 (Cdr 0) 2)))
    0)))).
Definition list_rev := Lam (list_rev_app 0 Nil).

Goal (reaches lam_step
             (Cfg (Exp (list_rev (Addr 0)) (Env nil))
                  (0 |-> Pair (Num 0) (Addr 1)
                  :* 1 |-> Pair (Num 1) (Addr 2)
                  :* 2 |-> Pair (Num 2) Nil)
                  1
                  Top)
             (eq (Cfg (Val (Addr 2))
                  (2 |-> Pair (Num 2) (Addr 1)
                  :* 1 |-> Pair (Num 1) (Addr 0)
                  :* 0 |-> Pair (Num 0) Nil)
                  1
                  Top)))%Z.
repeat tick.
apply rdone.
reflexivity.
Qed.