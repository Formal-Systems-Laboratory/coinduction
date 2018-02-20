Set Implicit Arguments.

Require Import String.
Require Import ZArith.

Require Import domains.
Require Import kstyle.
Require Import coinduction.
Require Import evaluator.

Coercion EVar : string >-> Exp.
Coercion ECon : Z >-> Exp.

Function evals n kcfg :=
  match n with
    | 0 => kcfg
    | S n => 
      match eval kcfg with
      | Some kcfg' => evals n kcfg'
      | None => kcfg
     end
  end.

Lemma evals_sound :
  forall n c (P : kcfg -> Prop), P (evals n c) -> reaches c P.
Proof.
induction n; simpl; intros;
[|pose proof (eval_sound c); destruct (eval c)];
eauto using done,step.
Qed.

Lemma eval_happy' : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus "x" "y")) nil)
            ("x" |-> 12%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty)
        (KCfg nil ("x" |-> 25%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty).
intros.
repeat (refine (step _ _);[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|]);
instantiate;simpl Zplus;apply done;reflexivity.
Qed.

Definition gcdLabel := 1%Z.
Definition doneLabel := 2%Z.

Definition gcdProg : Map Z Stmt :=
  gcdLabel |->
        SIf (BLe "a" "b")
          (SIf (BLe "b" "a")
               (Jump doneLabel)
               (Seq (SAssign "b" (EMinus "b" "a"))
                    (Jump gcdLabel)))
          (Seq (SAssign "a" (EMinus "a" "b"))
               (Jump gcdLabel)).
Lemma label_eval : forall env,
  steps (KCfg (kra (Jump gcdLabel) kdot)
            ("a" |-> 12%Z :* "b" |-> 13%Z :* env) mapEmpty gcdProg)
        (KCfg (kra (Jump doneLabel) kdot)
             ("a" |-> 1%Z :* "b" |-> 1%Z :* env) mapEmpty gcdProg).
intros. apply evals_sound with 307. simpl; repeat split; reflexivity.
Qed.

(* Some performance tests *)
Definition test_prop :=
  steps (KCfg (kra (SWhile (BLe 0%Z "x")
    (SAssign "x" (EPlus "x" (-1)%Z)))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Ltac kequiv_tac := repeat (apply conj);[reflexivity|simpl;equate_maps ..].
Ltac finish := apply done;kequiv_tac.

(* Using tactics alone *)
Lemma loop_test: test_prop.
Proof.
intros;
repeat (refine (step _ _);[econstructor (reflexivity || find_map_entry)|];instantiate;simpl Zplus);
finish.
Qed.

(* go step by step, but compute successor with eval rather than by tactics *)
Lemma loop_test': test_prop.
Proof.
Ltac step_eval :=refine (step _ _);[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|].
intros;repeat step_eval;simpl;finish.
Qed.

(* use multi-step evaluator, reduce with simpl *)
Lemma loop_test_evals_simpl : test_prop.
Proof.
intros;apply (evals_sound 1000);simpl;kequiv_tac.
Qed.

(* reduce with lazy *)
Lemma loop_test_evals_lazy: test_prop.
Proof.
intros;apply (evals_sound 1000);lazy;kequiv_tac.
Qed.

(* reduce with cbv *)
Lemma loop_test_evals_cbv: test_prop.
Proof.
intros;apply (evals_sound 1000);cbv;kequiv_tac.
Qed.

(* reduce with compute *)
Lemma loop_test_evals_compute : test_prop.
Proof.
intros;apply (evals_sound 1000);compute;kequiv_tac.
Qed.

(* reduce with vm_compute *)
Lemma loop_test_evals_vm_compute : test_prop.
Proof.
intros;apply (evals_sound 1000);vm_compute;kequiv_tac.
Qed.