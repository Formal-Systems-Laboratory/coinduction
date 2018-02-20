Require Import Bedrock.
Require Import semantics.
Require Import proof.

Definition incS : spec := SPEC("x") reserving 0
  PRE[V] [| True |]
  POST[R] [| R = V "x" ^+ $1 |].

Definition inc := bmodule "inc" {{
  bfunction "inc"("x") [incS]
    Return "x" + 1
  end with
  bfunction "inc'"("x","r") [SPEC("x") reserving 1
         PRE[_] [| True |] POST[_] [| True |]]
    "r" <-- Call "inc"!"inc"("x")        [PRE[_] Emp
         POST[_] Emp];;
    "r" <-- Call "inc"!"inc"("r")        [PRE[_] Emp
         POST[_] Emp];;
    Return "r"
  end
}}.

Require Import List.

Definition inc_block : block :=
  (Assign (LvMem (Sp + $ (0))%loc) Rp
  :: Binop Rv (LvMem (Sp + $ (4))%loc) Plus (RvImm $(1))
  :: Assign Rp (LvMem (Sp + $ (0))%loc)
  :: nil, Uncond Rp).

Inductive inc_spec stn (w : W) : inst_state -> (inst_state -> Prop) -> Prop :=
  inc_prop : forall st x,
   Some x = ReadWord stn (Mem st) (Regs st Sp ^+ $4) ->
   match ReadWord stn (Mem st) (Regs st Sp ^+ $0) with
   | Some _ => True
   | None => False
   end ->
   inc_spec stn w (start_block (w,st))
     (fun st' => match st' with
      | start_block (w', st'') => w' =
           Regs st Rp /\ Regs st'' Rv = x ^+ $1 /\
           (let stk := Regs st Sp in
            forall w', separated w' (Regs st Sp ^+ $0)
                  -> ReadWord stn (Mem st) w' = ReadWord stn (Mem st'') w')
      | _ => False
      end).

Check cancel.
Lemma cancel_right : forall (u v k : W), k ^+ u = k ^+ v -> u = v.
intros. rewrite (wplus_comm _ u), (wplus_comm _ v) in H.
apply cancel in H. assumption.
Qed.

Lemma cancel_add  : forall (v k : W), k = k ^+ v -> $0 = v.
intros. rewrite <- (wplus_unit k) in H at 1. rewrite wplus_comm in H.
apply cancel_right in H. assumption.
Qed.

Lemma read_write : forall stn mem addr r v,
  ReadWord stn mem addr = Some r ->
  WriteWord stn mem addr v = None -> False.
intros until v.
unfold ReadWord, WriteWord, mem_get_word, mem_set_word, ReadByte, WriteByte.
destruct (explode stn v) as (((? & ?) & ?) & ?).
simpl.
intro H.
destruct (mem (addr ^+ $(3)));[ |
  repeat match type of H with
   | match ?E with _ => _ end = _ => destruct E;[ | discriminate]
  end;discriminate].
destruct (weq (addr ^+ $(2)) (addr ^+ $3)) as [e | _];[apply cancel_right in e;discriminate | ].
destruct (mem (addr ^+ $(2)));[ |
  repeat match type of H with
   | match ?E with _ => _ end = _ => destruct E;[ | discriminate]
  end;discriminate].
destruct (weq (addr ^+ $(1)) (addr ^+ $2)) as [e | _];[apply cancel_right in e;discriminate | ].
destruct (weq (addr ^+ $(1)) (addr ^+ $3)) as [e | _];[apply cancel_right in e;discriminate | ].
destruct (mem (addr ^+ $(1)));[ |
  repeat match type of H with
   | match ?E with _ => _ end = _ => destruct E;[ | discriminate]
  end;discriminate].
destruct (weq addr (addr ^+ $1)) as [e | _];[apply cancel_add in e;discriminate | ].
destruct (weq addr (addr ^+ $2)) as [e | _];[apply cancel_add in e;discriminate | ].
destruct (weq addr (addr ^+ $3)) as [e | _];[apply cancel_add in e;discriminate | ].
destruct (mem addr);[ |
  repeat match type of H with
   | match ?E with _ => _ end = _ => destruct E;[ | discriminate]
  end;discriminate].
discriminate.
Qed.

Lemma inc_sound : forall (stn : settings) prog (w : W),
   prog w = Some inc_block -> sound (inst_rel stn prog) (inc_spec stn w).
intros. 
apply proved_sound. destruct 1.
destruct (ReadWord stn (Mem st) (Regs st Sp ^+ $0)) eqn:?;[clear H1|destruct H1].

eapply sstep. constructor. simpl. rewrite H. reflexivity.
destruct (WriteWord stn (Mem st) (Regs st Sp ^+ $0) (Regs st Rp)) eqn:?.
Focus 2. exfalso. apply (read_write _ _ _ _ _ Heqo Heqo0).
eapply dstep. constructor. simpl. rewrite Heqo0. reflexivity.
eapply dstep. constructor. simpl.
  SearchAbout ReadWord.
  symmetry in H0.
    assert (separated (Regs st Sp ^+ $4) (Regs st Sp ^+ $0)).
    apply const_separated;
      rewrite <- ?wplus_assoc, <- ?natToWord_plus; simpl;
      match goal with | [ |- not (eq (?x ^+ ?a) (?x ^+ ?b))] =>
        rewrite (wplus_comm x a), (wplus_comm x b);
        let H := fresh in intro H; apply wplus_cancel in H;discriminate
      end.
   rewrite <- (ReadWriteNe stn (Mem st) m _ _ _ H1 Heqo0) in H0.
   rewrite H0. reflexivity.
eapply dstep. constructor. simpl. rewrite rupd_ne by discriminate.
  rewrite (ReadWriteEq _ _ _ _ _ Heqo0). reflexivity.
eapply dstep. constructor. simpl. reflexivity.
eapply ddone.
  simpl.
split.
  rewrite rupd_eq. reflexivity.
split.
  rewrite rupd_ne by discriminate.  rewrite rupd_eq. reflexivity.
intros.
symmetry.
eapply ReadWriteNe.
eassumption.
eassumption.
Qed.

Goal LabelMap.Raw.elements (LabelMap.this (LabelMap.map snd (XCAP.Blocks inc)))
   = nil.
lazy.
Abort.

(*
   ("inc", Global "inc",
   ([Assign (LvMem (Sp + $ (0))%loc) Rp;
    Binop Rv (LvMem (Sp + $ (4))%loc) Plus $ (1);
    Assign Rp (LvMem (Sp + $ (0))%loc)], Uncond Rp));
   ("inc", Global "inc'",
   ([Assign (LvMem (Sp + $ (0))%loc) Rp;
    Binop Rv Sp Plus $ (12);
    Assign (LvMem (Rv + $ (4))%loc) (LvMem (Sp + $ (4))%loc);
    Binop Sp Sp Plus $ (12);
    Assign Rp ("inc", Local 12)]
   ,Uncond ("inc", Global "inc")));
   ("inc", Local 12,
   ([Binop Sp Sp Minus $ (12);
    Assign (LvMem (Sp + $ (8))%loc) Rv;
    Binop Rv Sp Plus $ (12);
    Assign (LvMem (Rv + $ (4))%loc) (LvMem (Sp + $ (8))%loc);
    Binop Sp Sp Plus $ (12);
    Assign Rp ("inc", Local 9)],
    Uncond ("inc", Global "inc")));
   ("inc", Local 9,
   ([Binop Sp Sp Minus $ (12); Assign (LvMem (Sp + $ (8))%loc) Rv;
    Assign Rv (LvMem (Sp + $ (8))%loc); Assign Rp (LvMem (Sp + $ (0))%loc)],
   Uncond Rp));

*)
