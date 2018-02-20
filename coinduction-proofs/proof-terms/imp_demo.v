Require Import ZArith.
Require Import String.

Require Import imp_domains.
Require Import imp_rules.

Require Import proof.
Require Import proof_automation.

Require Import map_zipper.

Open Scope Z_scope.
Open Scope string_scope.

(* Mostly generic equality solver *)
Lemma app_equal {A B} (f g : A -> B) (x y : A) : f = g -> x = y -> f x = g y.
congruence.
Qed.
Ltac equate_term :=
  reflexivity ||
  match goal with
  | [|- @eq Z _ _] => auto with zarith || ring
  | [|- @eq bool _ _] => auto
  | [|- @eq string _ _] => auto
  | _ => apply app_equal;equate_term
  end.

Ltac equate_maps' := 
 (repeat
 match goal with [|- ?l ~= ?r] =>
  match r with
  | context C [?k |-> ?v] =>
    has_evar v; match l with
    | context [k |-> ?v'] => unify v v'
    end
  end
 end);
 items;
 (apply equivRefl || apply equivUnit || apply equivUnitL).

Ltac domain_solver := solve[match goal with
  | [|- _ = _] => equate_term
  | [|- _ ~= _] => equate_maps';equate_term
  | _ => solve [auto with zarith | ring]
  end].

(* Reorder arguments of BoolSpec_ind for nicer proof certificates *)
Definition case_bool_spec {P Q b} (b0 : BoolSpec P Q b) 
   {P0 : bool -> Prop} (f : P -> P0 true) (f0 : Q -> P0 false) : P0 b :=
  @BoolSpec_ind P Q P0 f f0 b b0.

(* Depends on what Coq functions you use on primitive domains: *)
Ltac split_bool b := pattern b;match b with
| Z.leb ?x ?y => apply (case_bool_spec (Z.leb_spec x y));intro
end.

(* Actually language dependent: *)
Ltac split_stuck := idtac;match goal with
| [|- trans _ _ {| kcell := kra (k_inj_Stmt_KItem (If (BCon (k_wrap_zhBool_Bool ?b)) _ _)) _ |} _] =>
    split_bool b
end.

(* Specific to predicates used in a particular specification *)
Definition KCfg' code state : (kcfg -> Prop) :=
  fun c => match c with
  | KCfg code' state' => code' = code /\ state' ~= state
  end.
Lemma useKCfg' : forall code state (P : kcfg -> Prop),
  (forall state', state' ~= state -> P (KCfg code state')) ->
  forall k', KCfg' code state k' -> P k'.
intros until k'. destruct k', 1. subst. auto.
Qed.
Ltac trans_use_result := apply useKCfg';intros.

Ltac done_solver :=
  abstract (subst;simpl;repeat eexists;domain_solver).

(* Now the automation *)
Ltac run := domain_run domain_solver trans_use_result domain_solver split_stuck done_solver.
Ltac step := domain_step domain_solver trans_use_result domain_solver split_stuck.
Ltac solver := apply proved_sound;destruct 1;
               (eapply sstep;[econstructor(domain_solver)| ];instantiate;simpl;run).

Coercion k_wrap_zhInt_Int : Z >-> Int.
Coercion k_wrap_zhInt_KItem : Z >-> kitem.
Coercion k_token_Id : string >-> Id.
Coercion k_wrap_Id_KItem : Id >-> kitem.

Definition loop : Stmt :=
   While (Le (ACon 0) (Var "x"))
     (BStmt (Assign "x" (Add (Var "x") (ACon (-1))))).

Inductive loop_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  loop_claim : forall (x : Z) rest, loop_spec
          (KCfg (kra (k_wrap_Stmt_KItem loop) rest)
                (kra "x" kdot |-> kra x kdot :* mapEmpty))
     (fun c => match c with
      | KCfg code m => code = rest /\ exists (x':Z), (m ~= kra "x" kdot |-> kra x' kdot) /\ x' < 0
      end).

Arguments sstep [cfg cstep X k P k'] _ _.
Arguments sdone [cfg cstep X k P] _.
Arguments dstep [cfg cstep X k P k'] _ _.
Arguments ddone [cfg cstep X k P] _.
Arguments dtrans [cfg cstep X k P Q] _ _.

Lemma first_proof : sound kstep loop_spec.
solver.
Qed.
Set Printing Depth 100.
Set Printing Width 400.
Print first_proof.

Definition program : Pgm :=
  k_label_zqintzuZSzu ["x" : Id]
    ((Seq (Assign "x" (ACon 10))
     (Seq loop
          (Assign "x" (Add (Var "x") (ACon 10)))))).

Inductive program_spec : kcfg -> (kcfg -> Prop) -> Prop :=
  program_loop_claim : forall (x : Z) krest state state_rest,
      state ~= kra "x" kdot |-> kra x kdot :* state_rest -> x >= -1 ->
      program_spec (KCfg (kra (k_wrap_Stmt_KItem loop) krest) state)
                   (KCfg' krest (kra "x" kdot |-> kra (-1) kdot :* state_rest))
 | program_claim : program_spec
      (KCfg (kra (k_wrap_Pgm_KItem program) kdot) mapEmpty)
      (KCfg' kdot (kra "x" kdot |-> kra 9 kdot)).

Lemma second_proof : sound kstep program_spec.
solver.
Qed.

Definition sum_loop :=
  (While (Le (ACon 1) (Var "n"))
    (BStmt (Seq (Assign "s" (Add (Var "s") (Var "n")))
                (Assign "n" (Add (Var "n") (ACon (-1)%Z)))))).
Definition sum_code :=
  Seq (Assign "s" (ACon 0)) sum_loop.

Inductive sum_spec : kcfg -> (kcfg -> Prop) -> Prop :=
| mult_claim : forall (nv sv : Z) m state,
    state ~= (kra "n" kdot |-> kra nv kdot :* kra "s" kdot |-> kra sv kdot :* m) ->
    (nv >= 0)%Z ->
    forall krest,
    sum_spec (KCfg (kra (k_wrap_Stmt_KItem sum_loop) krest) state)
             (KCfg' krest (kra "n" kdot |-> kra 0 kdot
                          :* kra "s" kdot |-> kra (sv + nv * (nv + 1) / 2) kdot
                          :* m))
| sum_claim : forall (nv : Z) sv m state,
    state ~= (kra "n" kdot |-> kra nv kdot :* kra "s" kdot |-> sv :* m) ->
    (nv >= 0)%Z ->
    forall krest,
    sum_spec (KCfg (kra (k_wrap_Stmt_KItem sum_code) krest) state)
             (KCfg' krest (kra "n" kdot |-> kra 0 kdot
                          :* kra "s" kdot |-> kra (nv * (nv + 1) / 2) kdot
                          :* m))
.

Lemma sum_math nv :
   (nv * (nv + 1) / 2)%Z = (nv + (nv - 1) * (nv - 1 + 1) / 2)%Z.
Proof.
rewrite <- Z.div_add_l by auto with zarith.
apply f_equal2;ring.
Qed.

Lemma sum_proof : sound kstep sum_spec.
solver.

+ rewrite sum_math.
  run.

+ replace nv with 0%Z by auto with zarith.
  run.
Qed.
Print sum_proof.