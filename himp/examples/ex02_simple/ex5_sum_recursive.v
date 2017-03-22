Require Import simple.

Require Import List.
Require Import ZArith.

Definition sum_code :=
  SIf (BLe (EVar "n") (ECon 0))
      (SReturn (ECon 0))
      (SReturn (EPlus (EVar "n")
                      (ECall "sum_recursive"
                            (EMinus (EVar "n") (ECon 1) :: nil)))).

Definition sum_fun :=
  FunDef "sum_recursive" ("n" :: nil) sum_code.

Inductive sum_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  mult_claim : forall c, kcell c = kra (KStmt sum_code) kdot -> 
    forall nv m, store c ~=
      ("n" s|-> KInt nv :* m) ->
    (nv >= 0)%Z ->
    forall f, functions c ~=
      ("sum_recursive" s|-> KDefn sum_fun :* f) ->
    sum_spec c (returning c (nv * (nv + 1) / 2)).

Lemma sum_math nv :
   (nv * (nv + 1) / 2)%Z = (nv + (nv - 1) * (nv - 1 + 1) / 2)%Z.
Proof. 
replace (nv * (nv + 1))%Z with (nv * 2 + (nv - 1) * (nv - 1 + 1))%Z by ring.
auto using Z.div_add_l with zarith.
Qed.
Hint Resolve sum_math : done_hints.

Lemma mult_sound : sound kstep sum_spec.
Proof.
  simple_solver. replace nv with 0%Z by auto with zarith; simple_run.
Qed.

Definition sum_inf :=
  SIf (BCon false)
      (SReturn (ECon 0))
      (SReturn (EPlus (EVar "n")
                      (ECall "sum_recursive_inf"
                             (EMinus (EVar "n") (ECon 1) :: nil)))).

Definition sum_fun_inf :=
  FunDef "sum_recursive_inf" ("n" :: nil) sum_inf.

Inductive sum_inf_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  inf_claim : forall c, kcell c = kra (KStmt sum_inf) kdot ->
    forall nv m, store c ~=
      ("n" s|-> KInt nv :* m) ->
    forall f, functions c ~=
      ("sum_recursive_inf" s|-> KDefn sum_fun_inf :* f) ->
              sum_inf_spec c (fun r => False).

Lemma sum_inf_sound : sound kstep sum_inf_spec.
Proof. simple_solver. Qed.
