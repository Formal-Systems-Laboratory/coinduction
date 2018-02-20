Require Import stack.
Require Import patterns.

Fixpoint rep_seg lst (tailp p : Z) : MapPattern Z Z :=
 match lst with
    | nil => constraint (p = tailp)
    | x :: xs => constraint (p <> 0) :* existsP p',
        p |-> x :* (p + 1) |-> p' :* rep_seg xs tailp p'
  end%pattern.
Notation rep_list l := (rep_seg l 0).
