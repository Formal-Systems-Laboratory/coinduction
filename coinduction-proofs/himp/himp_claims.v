Require Export patterns.
Require Export proof.
Require Export himp_steps.

(* Environment or record entry, taking a string and kitem*)
Notation "x 's|->' y" :=
  (mapItem (kra (KId x) kdot) (kra (y : kitem) kdot))
  (at level 50, no associativity) : Map.

(* Heap entry, from an integer key and kitem value *)
Notation "x 'h|->' y" :=
  (mapItem (kra (KInt x) kdot) (kra (y : kitem) kdot))
  (at level 50, no associativity) : Map.
Notation "x 'h|->' y" :=
  (itemP (kra (KInt x) kdot) (kra (y : kitem) kdot))
  (at level 50, no associativity) : MapPattern.
(* Notations to help unify typed and untyped maps *)
Notation load_field v f := (EProject (ELoad (EVar v)) f).
(*
Notation funEntry name args body :=
   (name%string s|-> FunDef name args body).
 *)

Definition name (d : Defn) : string :=
  match d with
    | FunDef n _ _ => n
  end.
Definition fundefs (deps : list Defn) (d : Map k k) : Map k k :=
  fold_right (fun def m => (name def s|-> KDefn def) :* m) d deps.

Definition value_heap ret krest store stack frame funs mark
  : kcfg -> Prop := fun c' => match c' with
  | KCfg k' store' stack' heap' funs' mark' =>
      exists r', k' = kra r' krest /\ store' ~= store
      /\ stack' = stack  /\ heap' |= ret r' :* litP frame
      /\ funs' ~= funs /\ (mark' >= mark)%Z
  end.

Definition heap_fun (R : Spec kcfg) (deps : list Defn) (d:Defn) :
  forall (args : list KResult) (init_heap : MapPattern k k)
    (ret : Z -> MapPattern k k), Prop :=
  match d with FunDef name formals body =>
    fun args init_heap ret =>
      forall krest store stack heap funs mark otherfuns,
      funs ~= fundefs deps (name s|-> KDefn d) :* otherfuns ->
      (mark > 0)%Z ->
      forall frame,
      heap |= (init_heap :* litP frame) ->
      R (KCfg (kra (ECall name (map KResultToExp args)) krest)
              store stack heap funs mark)
        (value_heap (fun r => existsP v, constraint (r = KInt v)
                                         :* ret v)%pattern
              krest store stack frame funs mark)
   end.

Definition heap_gen_fun (R : Spec kcfg) (d:Defn) :
  forall (args : list KResult) (init_heap : MapPattern k k)
    (ret : kitem -> MapPattern k k), Prop :=
  match d with FunDef name formals body =>
    fun args init_heap ret =>
      forall krest store stack heap funs mark otherfuns,
      funs ~= name s|-> KDefn d :* otherfuns ->
      (mark > 0)%Z ->
      forall frame,
      heap |= (init_heap :* litP frame) ->
      R (KCfg (kra (ECall name (map KResultToExp args)) krest)
              store stack heap funs mark)
        (value_heap ret krest store stack frame funs mark)
   end.

Definition void_heap ret krest store stack frame funs mark
  : kcfg -> Prop := fun c' => match c' with
  | KCfg k' store' stack' heap' funs' mark' =>
      k' = krest /\ store' ~= store
      /\ stack' = stack  /\ heap' |= ret :* litP frame
      /\ funs' ~= funs /\ (mark' >= mark)%Z
  end.
Definition heap_void_fun (R : Spec kcfg) (deps : list Defn) (d:Defn) :
  forall (args : list KResult) (init_heap ret : MapPattern k k), Prop :=
  match d with FunDef name formals body =>
    fun args init_heap ret =>
      forall krest store stack heap funs mark otherfuns,
      funs ~= fundefs deps (name s|-> KDefn d) :* otherfuns ->
      (mark > 0)%Z ->
      forall frame,
      heap |= (init_heap :* litP frame) ->
      R (KCfg (kra (SCall name (map KResultToExp args)) krest)
              store stack heap funs mark)
        (void_heap ret krest store stack frame funs mark)
   end.

Definition return_heap ret stack frame funs mark : kcfg -> Prop :=
  fun c' => match c' with
  | KCfg k' store' stack' heap' funs' mark' =>
    exists r' krest, k' = kra (KStmt (SReturn r')) krest
    /\ stack' = stack /\ heap' |= ret r' :* litP frame
    /\ funs' ~= funs /\ (mark' >= mark)%Z
  end.

Definition suffix_claim (R : Spec kcfg)
    (body : k) (init_store : Map k k)
    (init_heap : MapPattern k k) 
    (final_heap : Z -> MapPattern k k) : Prop :=
  forall stack store store_rest heap frame funs mark,
     store ~= init_store :* store_rest ->
     heap |= (init_heap :* litP frame) ->
     (mark > 0)%Z ->
  R (KCfg body store stack heap funs mark)
    (return_heap (fun r => existsP v, constraint (r = ECon v)
                                      :* final_heap v)%pattern
                  stack frame funs mark).

Definition return_void_heap ret stack frame funs mark : kcfg -> Prop :=
  fun c' => match c' with
  | KCfg k' store' stack' heap' funs' mark' =>
    exists krest, k' = kra (KStmt SReturnVoid) krest
    /\ stack' = stack /\ heap' |= ret :* litP frame
    /\ funs' ~= funs /\ (mark' >= mark)%Z
  end.
Definition suffix_void_claim (R : Spec kcfg) (deps : list Defn)
    (body : k) (init_store : Map k k)
    (init_heap final_heap : MapPattern k k)  : Prop :=
  forall stack store store_rest heap frame funs otherfuns mark,
     funs ~= fundefs deps otherfuns ->
     store ~= init_store :* store_rest ->
     heap |= (init_heap :* litP frame) ->
     (mark > 0)%Z ->
  R (KCfg body store stack heap funs mark)
    (return_void_heap final_heap stack frame funs mark).

Fixpoint loop_tails (s : Stmt) (rest : k) : list k :=
  match s with
    | Seq s1 s2 => loop_tails s1 (kra s2 rest) ++ loop_tails s2 rest
    | SIf _ s1 s2 => loop_tails s1 rest ++ loop_tails s2 rest
    | SWhile _ s' => (kra s rest) :: loop_tails s' (kra s rest)
    | _ => nil
  end.

Definition body (def : Defn) :=
  match def with FunDef _ _ body => body end.

Definition heap_loop (R : Spec kcfg) (def : Defn) (n : nat) :
  Map k k -> MapPattern k k -> (Z -> MapPattern k k) -> Prop :=
  suffix_claim R (nth n (loop_tails (body def) kdot) kdot).

Definition heap_void_loop (R : Spec kcfg) (deps : list Defn) (def : Defn) (n : nat) :
  Map k k -> MapPattern k k -> MapPattern k k -> Prop :=
  suffix_void_claim R deps (nth n (loop_tails (body def) kdot) kdot).