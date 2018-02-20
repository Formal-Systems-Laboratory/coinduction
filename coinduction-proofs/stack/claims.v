Require Import patterns.
Require Import stack.

Set Implicit Arguments.

Fixpoint min_length (n : nat) {A} (l : list A) : Prop :=
  match n, l with
    | O, _ => True
    | S _, nil => False
    | S n', _ :: l' => min_length n' l'
  end.

Fixpoint stk_pat (n : nat) : Type :=
  match n with
    | O => MapPattern Z Z
    | S n' => Z -> stk_pat n'
  end.
Fixpoint stk_pat_app {n} (P : stk_pat n) (stk : list Z) :=
  match n return stk_pat n -> MapPattern Z Z with
    | O => fun P => P
    | S n' => fun P =>
                match stk with
                  | nil => constraint False
                  | x :: stk' => stk_pat_app (P x) stk'
                end
  end P.

Definition fun_claim (spec : cfg -> (cfg -> Prop) -> Prop) name body
  num_in (pre : stk_pat num_in) num_out (post : stk_pat num_out) :=
  forall rest stk rstk heap frame funs otherfuns mark,
    funs ~= name |-> body :* otherfuns ->
    min_length num_in stk ->
    mark > 0 ->
    heap |= stk_pat_app pre stk :* litP frame ->
    spec (Cfg (Call name :: rest) stk rstk heap funs mark)
         (fun c' => match c' with
           | Cfg code' stk' rstk' heap' funs' mark' =>
             code' = rest /\ min_length num_out stk'
            /\ skipn num_in stk = skipn num_out stk'
            /\ heap' |= stk_pat_app post stk' :* litP frame
            /\ rstk = rstk'
            /\ funs ~= funs'
            /\ mark' >= mark'
          end).

Fixpoint loops' i k : list (list Inst) :=
  match i with
    | If thn els =>
        let fix loops l k :=
          match l with
            | nil => nil
            | i :: l => loops' i (l++k) ++ loops l k
          end
        in loops thn k ++ loops els k
    | While cond body =>
        (i::k)::nil
    | _ => nil
  end.
Fixpoint loops (l : list Inst) : list (list Inst) :=
  match l with
    | nil => nil
    | i :: l' => loops' i l' ++ loops l'
  end.

Definition loop_claim (spec : cfg -> (cfg -> Prop) -> Prop) ix code
  num_in (pre : stk_pat num_in) num_out (post : stk_pat num_out) :=
  forall stk rstk heap frame funs mark,
    min_length num_in stk ->
    heap |= stk_pat_app pre stk :* litP frame ->
    mark > 0 ->
    spec (Cfg (nth ix (loops code) nil) stk rstk heap funs mark)
         (fun c' => match c' with
           | Cfg code' stk' rstk' heap' funs' mark' =>
               (exists rest', code' = Ret :: rest')
            /\ min_length num_out stk'
            /\ skipn num_in stk = skipn num_out stk'
            /\ heap' |= stk_pat_app post stk' :* litP frame
            /\ rstk = rstk'
            /\ funs ~= funs'
            /\ mark' >= mark'
          end).