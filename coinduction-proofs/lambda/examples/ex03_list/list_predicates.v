Require Import lambda.
Require Import patterns.

Fixpoint list_seg l (tailp p : val) : MapPattern loc val :=
  match l with
    | nil => constraint (tailp = p)
    | v :: vs => existsP l, constraint (p = Addr l) :*
        existsP p', l |-> Pair v p' :* list_seg vs tailp p'
  end%pattern.
Notation rep_list l := (list_seg l Nil).