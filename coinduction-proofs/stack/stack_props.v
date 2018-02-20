Require Import stack.

(* properties of the language definition *)

Definition cfg_equiv (k1 k2 : cfg) : Prop :=
  match k1, k2 with
    | Cfg k1 stk1 rstk1 heap1 funs1 mark1,
      Cfg k2 stk2 rstk2 heap2 funs2 mark2 =>
      k1 = k2 /\ stk1 = stk2 /\ rstk1 = rstk2
      /\ heap1 ~= heap2 /\ funs1 ~= funs2 /\ mark1 = mark2
  end.

Lemma step_resp_equiv_fwd : forall k1 k1' k2,
  cfg_equiv k1 k1' -> stack_step k1 k2 -> (exists k2', stack_step k1' k2').
intros.
destruct H0, k1'; simpl in H; decompose record H;clear H;subst;
try solve[eexists;econstructor(equate_maps)].
Qed.
