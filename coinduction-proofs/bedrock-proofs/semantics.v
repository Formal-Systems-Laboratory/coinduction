Require Import IL List.

Inductive block_rel (stn : settings) (prog : program) : state' -> state' -> Prop :=
  | run_block : forall st st', step stn prog st = Some st' -> block_rel stn prog st st'.
Lemma block_deterministic : forall stn prog st st1 st2,
  block_rel stn prog st st1 -> block_rel stn prog st st2 -> st1 = st2.
Proof.
intros. destruct H. destruct H0. congruence.
Qed.                                

Inductive inst_state : Set :=
  | start_block : state' -> inst_state
  | inside_block : block -> state -> inst_state
  .

Definition inst_step (stn : settings) (prog : program) (st : inst_state) : option inst_state :=
  match st with
  | start_block st' =>
    match prog (fst st') with
      | None => None
      | Some b => Some (inside_block b (snd st'))
    end
  | inside_block (nil, j) st =>
    match evalJmp stn st j with
      | Some w => Some (start_block (w,st))
      | None => None
    end
  | inside_block (i :: is, j) st =>
    match evalInstr stn st i with
      | Some st' => Some (inside_block (is,j) st')
      | None => None
    end
  end.

Inductive inst_rel (stn : settings) (prog : program) (st st' : inst_state) : Prop :=
  | run_inst : inst_step stn prog st = Some st' -> inst_rel stn prog st st'.

Lemma inst_det : forall stn prog st st1 st2,
   inst_rel stn prog st st1 -> inst_rel stn prog st st2 -> st1 = st2.
Proof.
destruct 1;destruct 1;congruence.
Qed.

Inductive inside_steps stn prog (st : inst_state) (st' : state') : Prop :=
  | finish : inst_rel stn prog st (start_block st') -> inside_steps stn prog st st'
  | inside_step : forall b mid,
      inst_rel stn prog st (inside_block b mid) ->
      inside_steps stn prog (inside_block b mid) st' ->
      inside_steps stn prog st st'
  .

Inductive star {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | empty : forall a, star R a a
  | step : forall a b, R a b -> forall c, star R b c -> star R a c.

Lemma inside_star stn prog st st' :
  inside_steps stn prog st st' -> star (inst_rel stn prog) st (start_block st').
Proof.
induction 1.
destruct H. eapply step;[|eapply empty]. constructor;eassumption.
eapply step;eassumption.
Qed.

Lemma refine_fwd : forall stn prog st st',
  block_rel stn prog st st' -> inside_steps stn prog (start_block st) st'.
Proof.
intros.
destruct H.
unfold IL.step in H.
destruct (prog (fst st)) eqn:?;[|discriminate].
apply inside_step with b (snd st).
  constructor. simpl. rewrite Heqo. reflexivity.
destruct st.
simpl in * |- *.
clear Heqo w.
destruct b.
revert s st' H.
induction l.
(* *)
simpl. intros.
destruct (evalJmp stn s j) eqn:?;[|discriminate].
apply finish. constructor. simpl. rewrite Heqo. congruence.
(* *)
intros. simpl in H.
destruct (evalInstr stn s a) eqn:?;[|discriminate].
specialize (IHl s0 st' H).
apply inside_step with (l, j) s0.
constructor. simpl. rewrite Heqo. reflexivity.
assumption.
Qed.

Lemma refine_rev : forall stn prog st st',
  inside_steps stn prog (start_block st) st' -> block_rel stn prog st st'.
destruct 1. destruct H.  simpl in H. destruct (prog (fst st)); discriminate.
constructor. simpl.
unfold IL.step. 
destruct H. simpl in H. destruct (prog (fst st));[|discriminate].
injection H;intros;subst;clear H.
revert H0.
destruct st. simpl. clear.
destruct b.
revert s. induction l.
destruct 1. destruct H. simpl in H. simpl.
destruct (evalJmp stn s j);[apply f_equal|];congruence.
destruct H. simpl in H. destruct (evalJmp stn s j);discriminate.
destruct 1. destruct H. simpl in H. destruct (evalInstr stn s a);discriminate.
destruct H. simpl in H. simpl. destruct (evalInstr stn s a);[|discriminate].
apply IHl. congruence.
Qed.

Lemma refine : forall stn prog st st',
  block_rel stn prog st st' <-> inside_steps stn prog (start_block st) st'.
Proof.
split; auto using refine_fwd, refine_rev.
Qed.