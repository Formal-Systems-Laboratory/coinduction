Require Import Bedrock.
Require List.

Require Import ConditionalTest.

Definition blocks :=
 Eval
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
           N.eq_dec N_rec N_rect Pos.eq_dec positive_rec positive_rect Pos.of_succ_nat
   makeBexp size
   inc incS]
  in (LabelMap.Raw.elements_aux nil (LabelMap.this (XCAP.Blocks alwaysZero))).


Print always_blocks.
(* XXXX
   These commands appear in the definition of the vcgen tactic
   for the examples, but they don't seem to help me:
   running <vcgen_simp;sep_auto> seems to work
   just as well or poorly as  <vcgen_simp;vcgen_rewrites;sep_auto>
   anywhere I mention vcgen_simp in this file
 *)
Ltac vcgen_rewrites :=
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold.

Definition always_just_code : list (label * block) :=
 Eval vm_compute in
 (LabelMap.Raw.elements_aux nil (LabelMap.this (LabelMap.map snd (XCAP.Blocks alwaysZero)))).
Print always_just_code.

Definition always_blocks : list (label * (assert * block)) :=
 Eval vm_compute in
 (LabelMap.Raw.elements_aux nil (LabelMap.this (XCAP.Blocks alwaysZero))).
Print always_blocks.

Definition test_blocks : list (label * (assert * block)) :=
 LabelMap.Raw.elements_aux nil (LabelMap.this (XCAP.Blocks alwaysZero)).

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

Lemma always_proof :
  forall (claims : (settings*state') -> ((settings*state') -> Prop) -> Prop)
         (spec: codeSpec W (settings*state)) prog stn
    (Hlabels: List.Forall (has_block stn spec prog) always_blocks)
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
      end) always_blocks.
unfold always_blocks, alwaysZero;intros;repeat constructor.


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
match goal with
 | [ |- match Labels ?stn ?l with _ => _ end] =>
  pose Hlabels as Hlabel;get_label stn l Hlabel
 end;destruct Hlabel as [Hlabel_p _];intros;
match goal with
   [ H : _ = Some ?w |- step _ _ (_,(?w,_)) _] =>
   clear H
end.




Check Forall_inv.
Lemma Forall_tl : forall A (P : A -> Prop) a l,
  List.Forall P (a :: l) -> List.Forall P l.
inversion 1. assumption.
Qed.

Require Import Bool.

Goal test_blocks = nil.
unfold test_blocks, alwaysZero.
unfold bmodule_.
lazy [map app toCmd
      Seq Instr
      Assign' Cond Fail
      Goto
     regInL lvalIn immInR labelIn
      makeBexp COperand1 COperand2 CTest].
unfold Fail_.
unfold Straightline_.
Print bmodule_.
Print StructuredModule.bmodule_.
unfold Seq_ at 1.
Print COperand1.
Print Conditional.Test.
Print makeBexp.
Print Seq_.

Print Straightline_.
lazy [Cond].
Locate "_ <- _".
Print Assign'.
Print Instr.
Print Seq.
unfold Seq.
lazy [bmodule_
  map app imps
  setArgs Programming.Reserved Programming.Formals Programming.Precondition
  importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
  ].
unfold bmodule_, StructuredModule.bmodule_, StructuredModule.blocks.
lazy [bmodule_ StructuredModule.bmodule_ StructuredModule.blocks

  map app imps
  LabelMap.add Entry Blocks Postcondition VerifCond
  ].
  setArgs Programming.Reserved Programming.Formals Programming.Precondition
  importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
  List.fold_left ascii_lt string_lt label'_lt
  LabelKey.compare' LabelKey.compare LabelKey.eq_dec
  LabelMap.find
  toCmd Seq Instr Diverge Fail Skip Assert_
  Programming.If_ Programming.While_ Goto Programming.Call_ RvImm'
  Assign' localsInvariant
  regInL lvalIn immInR labelIn variableSlot string_eq ascii_eq
  andb eqb qspecOut
  ICall_ Structured.ICall_
  Assert_ Structured.Assert_
  LabelMap.Raw.find LabelMap.this LabelMap.Raw.add
  LabelMap.empty LabelMap.Raw.empty string_dec
  Ascii.ascii_dec string_rec string_rect sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
  fst snd labl
  Ascii.N_of_ascii Ascii.N_of_digits N.compare Nmult Pos.compare Pos.compare_cont
  Pos.mul Pos.add LabelMap.Raw.bal
  Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
  ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max LabelMap.Raw.height
  ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max
  ZArith_dec.Zcompare_rec ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
  ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect
  COperand1 CTest COperand2 Pos.succ
  makeVcs

  Cond_ Cond
  Lambda__ Lambda_

  Wrap.Wrap
  Parse1 ParseOne ParseOne'
  Query ForArray
].
vcgen_simp.
intros.


o