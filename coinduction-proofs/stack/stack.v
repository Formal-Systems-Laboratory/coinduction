Require Export maps.
Require Export ZArith.
Require Export String.
Require Export List.

Open Scope string_scope.
Open Scope list_scope.
Open Scope Z.

Inductive Inst : Set :=
  | Dup : nat -> Inst
  | Roll : nat -> Inst
  | Drop
  | Push : Z -> Inst
  | Binop : (Z -> Z -> Z) -> Inst
  | While : list Inst -> list Inst -> Inst
  | If : list Inst -> list Inst -> Inst
  | Load
  | Store
  | Call : string -> Inst
  | Ret : Inst
  | Alloc : nat -> Inst
  | Dealloc : Inst.

Definition Swap := Roll 1.
Definition Over := Dup 1.
Definition Nip := Swap::Drop::nil.
Definition Rot := Roll 2::Roll 2::nil.
Definition Plus1 := Push 1::Binop Z.add::nil.

Structure cfg := Cfg {
  code : list Inst;
  stack : list Z;
  rstack : list (list Inst);
  heap : Map Z Z;
  functions : Map string (list Inst);
  alloc_next : Z
  }.

(* Compute a map for initial bindings in Alloc,
   with some extra work to make a pretty term *)
Definition offset (base :Z) (n : nat) : Z :=
  match n with
    | O => base
    | _ => (base + Z.of_nat n)%Z
  end.
Fixpoint init n ix base : Map Z Z :=
  match n with
    | O => mapEmpty
    | S O => offset base ix |-> 0%Z
    | S n' => offset base ix |-> 0%Z :* init n' (S ix) base
  end.

Local Notation basic_step step
    code  stk  heap  mark
    code2 stk2 heap2 mark2:=
  (forall rstk funs,
     step (Cfg code  stk  rstk heap  funs mark)
          (Cfg code2 stk2 rstk heap2 funs mark2)).
Local Notation inst_step step inst stk stk2 :=
  (forall rest heap mark, basic_step step
    (inst::rest) stk heap mark rest stk2 heap mark).

Generalizable Variables n x y stk.
Inductive stack_step : cfg -> cfg -> Prop :=
  | dup : `(inst_step stack_step (Dup n)
      stk (nth_default 0 stk n :: stk))
  | roll : `(inst_step stack_step (Roll n)
      (x::stk) (firstn n stk ++ x :: skipn n stk))
  | drop : `(inst_step stack_step Drop
      stk (tl stk))
  | push : `(inst_step stack_step (Push x)
      stk (x :: stk))
  | binop : forall f, `(inst_step stack_step (Binop f)
      (x :: y :: stk) (f y x :: stk))
  | while : forall test body rest stk h m, basic_step stack_step
      (While test body::rest) stk h m
      (test++If (body++While test body::nil) nil::rest) stk h m
  | ifz : forall x t f rest stk h m, basic_step stack_step
      (If t f::rest)                           (x::stk) h m
      ((if Zneq_bool x 0 then t else f)++rest)     stk  h m
  | load : forall x rest stk v heap heap' mark,
      heap ~= x |-> v :* heap' -> basic_step stack_step
        (Load::rest) (x::stk) heap              mark
               rest  (v::stk) (x|-> v :* heap') mark
  | store : forall p v rest stk v' heap heap' mark,
      heap ~= p |-> v' :* heap' -> basic_step stack_step
        (Store::rest) (p::v::stk) heap               mark
                rest         stk  (p |-> v :* heap') mark
  | alloc1 : forall n rest stk heap m, basic_step stack_step
      (Alloc n::rest) stk                 heap   m
       rest       (m::stk) (init n 0 m :* heap) (Z.of_nat n + m)%Z
  | dealloc : forall rest x v stk heap heap' mark,
      heap ~= x |-> v :* heap' -> basic_step stack_step
        (Dealloc::rest) (x::stk) heap  mark
                  rest      stk  heap' mark
  | call : forall f body rest stk rstk heap funs funs' mark,
      funs ~= f |-> body :* funs' -> stack_step
         (Cfg (Call f::rest) stk        rstk  heap funs mark)
         (Cfg body           stk (rest::rstk) heap funs mark)
  | ret : forall rest rbody stk rstk heap funs mark, stack_step
      (Cfg (Ret::rest) stk (rbody::rstk) heap funs mark)
      (Cfg rbody       stk         rstk  heap funs mark).
Arguments nth_default / : simpl nomatch.