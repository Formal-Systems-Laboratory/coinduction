Require Export himp_claims.
Require Export patterns.

(** A list node in memory *)
Notation list_node val next :=
  (KStruct (Struct ("val" s|-> KInt val :* "next" s|-> KInt next))).
(** And some abbreviations for code working with list nodes *)
Notation arr_val v := (EProject (ELoad (EVar v)) "val").
Notation arr_next v := (EProject (ELoad (EVar v)) "next").
Notation build_node v p := (EBuild ("val" s|-> v :* "next" s|-> p)).

Fixpoint rep_seg (val : list Z) (tailp p : Z) : MapPattern k k :=
  match val with
    | nil => constraint (p = tailp)
    | x :: xs => constraint (p <> 0) :* existsP p',
        p h|-> list_node x p' :* rep_seg xs tailp p'
  end%pattern.
Notation rep_list l := (rep_seg l 0).