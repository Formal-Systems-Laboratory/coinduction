Require Import Bedrock.
Require List.

Require Import AutoSep.

(* Issues getting symbolic execution are marked with XXXX *)
(* Issues with reification(?) are marked with YYYY *)

Definition incS : spec := SPEC("x") reserving 0
  PRE[V] [| True |]
  POST[R] [| R = V "x" ^+ $1 |].

Definition inc := bmodule "inc" {{
  bfunction "inc"("x") [incS]
    Return "x" + 1
  end
}}.

(* YYYY
   These commands appear in the definition of the vcgen tactic
   for the examples, but they don't seem to help me:
   running <vcgen_simp;sep_auto> seems to work
   just as well or poorly as  <vcgen_simp;vcgen_rewrites;sep_auto>
   anywhere I mention vcgen_simp in this file
 *)
Ltac vcgen_rewrites :=
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold.

(*
  Ltac getblocks_simp :=
    cbv beta iota zeta
     delta [map app imps LabelMap.add Entry Blocks Postcondition VerifCond
           Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Structured.If_
           Structured.While_ Goto_ Structured.Call_ IGoto setArgs Reserved
           Formals Precondition importsMap fullImports buildLocals blocks union
           N.add N.succ Datatypes.length N.of_nat fold_left ascii_lt string_lt
           label'_lt LabelKey.compare' LabelKey.compare LabelKey.eq_dec
           LabelMap.find toCmd Seq Instr Diverge Fail Skip Assert_ If_ While_
           Goto Call_ RvImm' Assign' localsInvariant regInL lvalIn immInR
           labelIn variableSlot string_eq ascii_eq andb Bool.eqb qspecOut
           ICall_ Structured.ICall_ Assert_ Structured.Assert_
           LabelMap.Raw.find LabelMap.this LabelMap.Raw.add LabelMap.empty
           LabelMap.Raw.empty string_dec Ascii.ascii_dec string_rec string_rect
           sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
           Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym fst
           snd labl Ascii.N_of_ascii Ascii.N_of_digits N.compare N.mul
           Pos.compare Pos.compare_cont Pos.mul Pos.add LabelMap.Raw.bal
           Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
           ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max
           LabelMap.Raw.height ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add
           Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max ZArith_dec.Zcompare_rec
           ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
           ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect COperand1 CTest
           COperand2 Pos.succ makeVcs Cond_ Cond Lambda__ Lambda_ Wrap.Wrap
           Parse1 ParseOne ParseOne' Query ForArray
           LabelMap.elements LabelMap.Raw.elements LabelMap.Raw.elements_aux XCAP.Blocks
           bmodule_ StructuredModule.bmodule_ StructuredModule.blocks
           LabelMap.fold LabelMap.Raw.fold Generate
           N.eq_dec N_rec N_rect Pos.eq_dec positive_rec positive_rect Pos.of_succ_nat].
 *)

Definition inc_blocks : list (label * (assert * block)) :=
Eval cbv beta iota zeta
     delta [map app imps LabelMap.add Entry Blocks Postcondition VerifCond
           Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Structured.If_
           Structured.While_ Goto_ Structured.Call_ IGoto setArgs Reserved
           Formals Precondition importsMap fullImports buildLocals blocks union
           N.add N.succ Datatypes.length N.of_nat fold_left ascii_lt string_lt
           label'_lt LabelKey.compare' LabelKey.compare LabelKey.eq_dec
           LabelMap.find toCmd Seq Instr Diverge Fail Skip Assert_ If_ While_
           Goto Call_ RvImm' Assign' localsInvariant regInL lvalIn immInR
           labelIn variableSlot string_eq ascii_eq andb Bool.eqb qspecOut
           ICall_ Structured.ICall_ Assert_ Structured.Assert_
           LabelMap.Raw.find LabelMap.this LabelMap.Raw.add LabelMap.empty
           LabelMap.Raw.empty string_dec Ascii.ascii_dec string_rec string_rect
           sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
           Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym fst
           snd labl Ascii.N_of_ascii Ascii.N_of_digits N.compare N.mul
           Pos.compare Pos.compare_cont Pos.mul Pos.add LabelMap.Raw.bal
           Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
           ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max
           LabelMap.Raw.height ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add
           Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max ZArith_dec.Zcompare_rec
           ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
           ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect COperand1 CTest
           COperand2 Pos.succ makeVcs Cond_ Cond Lambda__ Lambda_ Wrap.Wrap
           Parse1 ParseOne ParseOne' Query ForArray
           LabelMap.elements LabelMap.Raw.elements LabelMap.Raw.elements_aux XCAP.Blocks
           bmodule_ StructuredModule.bmodule_ StructuredModule.blocks
           LabelMap.fold LabelMap.Raw.fold Generate
           N.eq_dec N_rec N_rect Pos.eq_dec positive_rec positive_rect Pos.of_succ_nat
           inc incS] in  (LabelMap.Raw.elements_aux nil (LabelMap.this (XCAP.Blocks inc))).

Inductive StnStep prog (stn_st : settings*state') : settings*state' -> Prop :=
  stn_step : forall st',
    IL.step (fst stn_st) prog (snd stn_st) = Some st' ->
    StnStep prog stn_st (fst stn_st , st').

Inductive step {cfg : Set} (semantics : cfg -> cfg -> Prop)
       (X : cfg -> (cfg -> Prop) -> Prop)
       (k : cfg) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step semantics X k P
  | sstep : forall k', semantics k k' -> X k' P -> step semantics X k P
  .

Definition has_block stn spec prog (lb : label * (assert * block)) :=
  match Labels stn (fst lb) with
  | Some w => prog w = Some (snd (snd lb)) /\ spec w = Some (fst (snd lb))
  | None => False
  end.

Check Forall_inv.
Lemma Forall_tl : forall A (P : A -> Prop) a l,
  List.Forall P (a :: l) -> List.Forall P l.
inversion 1. assumption.
Qed.

(* Bedrock's "runs forever" notion of safety is captured
  by a (weak)reachability claim with postcondition False.

  This is a modular coinductive argument for the correctness of inc.
  In particular, the assumptions are a set of claims and a codeSpec
  environment (used to interpret PropX.spec predicates), and the
  assumptions that the set of claims include safety of the basic blocks
  of inc and any claims of the codeSpec environment.
  The conclusion is that any state which is just about to execute one
  of the basic blocks of inc and meets the corresponding precondition
  will end up after one computation step in a state whose safety is
  included in the claims.

  For an overall safety proof of any linked set of claims including
  safety of the basic blocks of inc, this lemma can be used as part
  of the overall stability argument to show that the claims about inc
  are supported.
 *)
Lemma inc_proof :
  forall (claims : (settings*state') -> ((settings*state') -> Prop) -> Prop)
         (spec: codeSpec W (settings*state)) prog stn
    (Hlabels: List.Forall (has_block stn spec prog) inc_blocks)
    (Hspec:forall w P,
      spec w = Some P ->
      forall st,
        interp spec (P (stn,st)) ->
        claims (stn,(w,st)) (fun _:(settings*state') => False)),
    List.Forall (fun lp =>
      match Labels stn (fst lp) with
      | None => False
      | Some w =>
        forall st,
          interp spec (fst (snd lp) (stn,st)) ->
          step (StnStep prog) claims (stn,(w,st)) (fun _:(settings*state') => False)
      end) inc_blocks.

(* Split the conclusion into goal for each case,
   and introduce a hypothesis that label lookups succeed *)
  (* This tactic grabs the right case out of (a copy of) Hlabels,
     introducing hypotheses that a particular label is assigned
     an address, and that address is assigned the correct code
     and predicate *)
Ltac get_label stn l H :=
  unfold inc_blocks in H;
  repeat match type of H with
    | List.Forall _ ((l,_) :: _) => apply Forall_inv in H;
           unfold has_block in H;simpl in H;
           destruct (Labels stn l) eqn:?;[ |tauto]
    | _ => apply Forall_tl in H
  end.
intros;repeat constructor;simpl;
match goal with
 | [ |- match Labels ?stn ?l with _ => _ end] =>
  pose Hlabels as Hlabel;get_label stn l Hlabel
 end;destruct Hlabel as [Hlabel_p _];intros;
match goal with
   [ H : _ = Some ?w |- step _ _ (_,(?w,_)) _] =>
   clear H
end.

(* This block does not need any special tactic support.
   There are no instructions to run, and it ends with an
   unconditional jump to a label with the same predicate *)
 (* Extract information on the next block from Hlabels *)
match goal with [Hlabel_p : prog ?w = Some (_, Uncond (RvLabel ?l))
   |- step _ _ (_, (?w, _)) _ ] =>
  get_label stn l Hlabels;destruct Hlabels as [_ Hlabels]
end.
eapply sstep. constructor. unfold IL.step.
   simpl. rewrite Hlabel_p. simpl. rewrite evalInstrs_nil.
match goal with
  [ H : Labels _ ?E = _ |- context [ match Labels _ ?E with _ => _ end ] ] =>
  rewrite H;clear H
end. reflexivity.
simpl.
eapply Hspec. 
eassumption.
eassumption.

(* This block has a False precondition, making it trivial *)
post.

(* 
   This block is actually executes last.
   It doesn't end by jumping to a fixed block but to a stored pointer,
   so we need to use tactics to gain hypotheses that the target
   actually exists and has a specification, and that we can meet it.
 XXXX
  There are no instructions in this block, so there's no trouble
  relating the state before and after evalInstrs, but in later blocks
  we'll see sep_auto or evaluate auto_ext leaving goals that
  seem unprovable. *)
eapply sstep. constructor. unfold IL.step.
  simpl. rewrite Hlabel_p. simpl. rewrite evalInstrs_nil.
  reflexivity.
revert H. vcgen_simp.
clear Hlabel_p Hlabels. intro. sep_auto.
(* YYYY Some of the current hypotheses apparently interact badly
    with the proof automation, but in other places similar hypotheses
    are not a problem
   running sep_auto here without clear produces
   Error: Tactic failure: bad enough (level 9996). *)
eapply Hspec.
(* using Hspec leaves two goals, of showing that the
   target address has the claimed specification,
   and that the current state satisfies the specification
 *)
 (* For the first, we use some of the facts left by sep_auto *)
match goal with [H : ?L = ?R |- spec ?L = _] => rewrite H;eassumption end.
 (* For the other goal, conclude by running these steps
    taken from sep_auto (in sep') *)
repeat (descend;step auto_ext).

(* This block is the first which actually contains instructions.
   We conclude that evalInstrs succeeds by making a case distinction and
   using sep_auto to refute the None case.
  *)
match goal with
 [ Hprog : prog ?w = Some (?insts, _) |- step _ _ (_, (?w, _)) _] =>
 let Heval := fresh "Heval" in
   destruct (evalInstrs stn st insts) eqn:Heval;
   [ | contradict Heval;
       repeat match goal with [H : interp _ _ |- _] => revert H end;
       clear;vcgen_simp;sep_auto ]
end.
(* 
   The commands between this comment and the next work whether
   or not you run these commented commands
   XXXX
   Running the commented commands here already seems to accomplish
   some symbolic execution, but the hypotheses it leaves don't
   seem to be strong enough to finish.
   YYYY
   This inlines post and evaluate auto_ext instead of using sep_auto
   because leaving Hlabels as a hypothesis interferes with the
   tactic, but I need to keep it around.
revert H Hlabel_p Heval.
  vcgen_simp;post;revert Hlabels;evaluate auto_ext;intro.
  *)
match type of Hlabel_p with _ = Some (_, Uncond (RvLabel ?l))
  => get_label stn l Hlabels;destruct Hlabels as [_ Hlabels]
end.
apply sstep with (k':=(stn,(w0,s))). constructor. simpl.
  unfold IL.step;simpl;
  repeat (match goal with
  [ H : ?L = _ |- context [ match ?L with _ => _ end ] ] => rewrite H
  end;simpl);reflexivity.
clear Hlabel_p Heqo. apply (Hspec _ _ Hlabels);clear -H Heval. simpl.
Inductive hide (P : Prop) : Prop := Hide : P -> hide P.
apply Hide in Heval. sep_auto. sep_auto. assumption. destruct Heval. assumption.
(* XXXX
   The current goal is obviously true (if we didn't run symbolic
   execution above), but sep_auto doesn't solve it,
   at least not when run like this.

try (revert H Heval);vcgen_simp;sep_auto.

   It seems the symbolic execution (whether from the commands in the
   previous comment or from "evaluate auto_ext" in the
   implementation of sep_auto) doesn't provide a strong enough
   hypothesis relating the heaps of the states before and after
   running the instructions of this block.
   (The "try" ensures the commands run whether or not we
    ran the commands from the previous comment)

  Instead, I just directly finish with the constructors of valid :(
  *)
eapply Exists_I. apply And_I. eassumption. apply Inj_I. assumption.

(* This block again has no instructions,
   so there's no problem with using sep_auto to show that
   the precondition of the next block is met
 *)
match type of Hlabel_p with _ = Some (_, Uncond (RvLabel ?l))
  => get_label stn l Hlabels;destruct Hlabels as [_ Hlabels]
end.
eapply sstep. constructor.
  unfold IL.step;simpl;
  repeat (match goal with
  [ H : ?L = _ |- context [ match ?L with _ => _ end ] ] => rewrite H
  end;simpl);reflexivity.
simpl.
specialize (Hspec _ _ Hlabels);apply Hspec.
(* YYYY It's a bit surprising it wasn't necessary to clear "Hlabel_p" here.
     I suppose it's because the instructions are nil this time? *)
clear Hlabels.
revert H;vcgen_simp;sep_auto.

(* This block again has some actual code *)
match type of Hlabel_p with _ = Some (_, Uncond (RvLabel ?l))
  => get_label stn l Hlabels;destruct Hlabels as [_ Hlabels]
end.
specialize (Hspec _ _ Hlabels). simpl in Hspec. clear Hlabels.
match type of Hlabel_p with _ = Some (?I, _)
  => let Heval:=fresh "Heval" in
   destruct (evalInstrs stn st I) eqn:Heval;
   [ | contradict Heval;
       repeat match goal with [H : interp _ _ |- _] => revert H end;
       clear;vcgen_simp;sep_auto ]
end.
eapply sstep.
constructor. unfold IL.step. simpl.
  repeat (match goal with
  [ H : ?L = _ |- context [ match ?L with _ => _ end ] ] => rewrite H
  end;simpl);reflexivity.
apply Hspec. revert Heval H. clear.
(* XXXX Again, sep_auto can't solve this.
  This time around the second goal needs eassumption, but
  it otherwise seems very similar.
vcgen_simp;sep_auto;[ |eassumption|assumption].
 *)
intros. eapply Exists_I. apply And_I. eassumption. apply Inj_I. assumption.
Qed.