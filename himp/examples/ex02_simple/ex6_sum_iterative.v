Require Import simple.

(* Require Import equate_map_reflection. *)

Require Import List.
Require Import ZArith.

Definition sum_loop :=
  (SWhile (BLt (ECon 0) (EVar "n")) 
          (Seq (SAssign "s" (EPlus (EVar "s") (EVar "n")))
               (SAssign "n" (EPlus (EVar "n") (ECon (-1)%Z))))).
Definition sum_code :=
  Seq (SAssign "s" (ECon 0))
 (Seq sum_loop
      (SReturn (EVar "s"))).

Inductive sum_spec : kcfg -> (kcfg -> Prop) -> Prop :=
| mult_claim : forall c, kcell c = kra (KStmt sum_code) kdot -> 
    forall nv sv m, store c ~=
      ("n" s|-> KInt nv :* "s" s|-> KInt sv :* m) ->
    (nv >= 0)%Z ->
    sum_spec c (returning c (nv * (nv + 1) / 2))
| loop_claim : forall c, kcell c = kra (KStmt sum_loop)
                                  (kra (KStmt (SReturn (EVar "s"))) kdot) ->
    forall nv sv m, store c ~=
      ("n" s|-> KInt nv :* "s" s|-> KInt sv :* m) ->
    (nv >= 0)%Z ->
    sum_spec c (returning c (sv + nv * (nv + 1) / 2))
.

Lemma sum_math nv :
   (nv * (nv + 1) / 2)%Z = (nv + (nv - 1) * (nv - 1 + 1) / 2)%Z.
Proof.
rewrite <- Z.div_add_l by auto with zarith.
apply f_equal2;ring.
Qed.

Lemma mult_sound : sound kstep sum_spec.
Proof.
simple_solver.
+ rewrite (sum_math nv) by auto with zarith; simple_run.
+ replace nv with 0%Z by auto with zarith; simple_run.
Qed.

Definition sum_inf :=
  (SWhile (BCon true) 
          (Seq (SAssign "s" (EPlus (EVar "s") (EVar "n")))
               (SAssign "n" (EPlus (EVar "n") (ECon (-1)%Z))))).

Definition sum_code_inf :=
  Seq (SAssign "s" (ECon 0))
 (Seq sum_inf
      (SReturn (EVar "s"))).

Inductive sum_inf_spec : kcfg -> (kcfg -> Prop) -> Prop :=
| inf_claim : forall c, kcell c = kra (KStmt sum_inf)
                                      (kra (KStmt (SReturn (EVar "s"))) kdot) ->
    forall nv sv m, store c ~=
      ("n" s|-> KInt nv :* "s" s|-> KInt sv :* m) ->
    sum_inf_spec c (fun r => False).

Lemma sum_inf_proof : sound kstep sum_inf_spec.
Proof. simple_solver. Qed.
