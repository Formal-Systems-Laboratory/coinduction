Require Import list_examples.

Require Import ho_proof.

Definition oddDef :=
  FunDef "odd" ["x"]
         (SIf (BEq "x" 0) (SReturn (ECon 0))
              (SReturn (ECall "even" [EMinus (EVar "x") (ECon 1)]))).
Definition evenDef :=
  FunDef "even" ["x"]
         (SIf (BEq "x" 0) (SReturn (ECon 1))
              (SReturn (ECall "odd" [EMinus (EVar "x") (ECon 1)]))).

(* spec claims that calling def computes the same result as f
   as long as deps and def are included in the funs *)
Definition z_spec (f:Z -> bool) spec deps def :=
  forall y, heap_fun spec deps def [Int y] emptyP (fun r => constraint (r = if f y then 1 else 0)).

Lemma heap_fun_mono (spec1 : Spec kcfg) (spec2 : Spec kcfg):
  forall deps d args init_heap ret,
    heap_fun spec1 deps d args init_heap ret ->
    (forall x P, spec1 x P -> spec2 x P) ->
    heap_fun spec2 deps d args init_heap ret.
Proof.
  intros. unfold heap_fun. destruct d. intros. apply H0. eapply H; eauto.
Qed.

Lemma z_spec_mono (spec1 : Spec kcfg) (spec2 : Spec kcfg):
  forall f deps def,
     z_spec f spec1 deps def ->
     (forall x P, spec1 x P -> spec2 x P) ->
     z_spec f spec2 deps def.
Proof.
  unfold z_spec, heap_fun. firstorder. eapply heap_fun_mono with spec1.
  unfold heap_fun. firstorder. assumption.
Qed.
  
Inductive ho_spec (A : Spec kcfg): Spec kcfg :=
| even_claim :
    forall OddDef,
      name OddDef = "odd" ->
      (z_spec Z.odd A [evenDef] OddDef) ->
      z_spec Z.even (ho_spec A) [OddDef] evenDef
| odd_claim :
    forall EvenDef,
      name EvenDef = "even" ->
      (z_spec Z.even A [oddDef] EvenDef) ->
      z_spec Z.odd (ho_spec A) [EvenDef] oddDef
| even_final :
    z_spec Z.even (ho_spec A) [oddDef] evenDef.
  
Inductive make_mono (F : Spec kcfg -> Spec kcfg) X: Spec kcfg :=
  mono_claim :
    forall A : Spec kcfg,
      (forall x P, A x P -> X x P) ->
      forall x P, F A x P -> make_mono F X x P.

Definition make_increasing : forall (F : Spec kcfg -> Spec kcfg) A x P,
    F A x P -> make_mono F A x P :=
  fun F A x P => mono_claim _ _ _ (fun _ _ H => H) x P.

Lemma made_mono : forall (F : Spec kcfg -> Spec kcfg),
   forall A B, (forall x P, A x P -> B x P) ->
               (forall x P, make_mono F A x P -> make_mono F B x P).
Proof. intros. destruct H. econstructor;eauto. Qed.

Lemma my_ho_spec_mono : forall (A : Spec kcfg) x P, make_mono ho_spec A x P -> ho_spec A x P.
Proof.
  destruct 1. destruct H0;econstructor(solve[eauto using z_spec_mono]).
Qed.

  
(* read manual on set implicit args *)
(* b = step cstep *)
Inductive T (cfg : Set) (cstep : cfg -> cfg -> Prop)
          (F : Spec cfg -> Spec cfg)
          (X : Spec cfg) (k : cfg) (P : cfg -> Prop) : Prop :=
  (* sdone step (c in P) *)
  tdone : P k -> T cfg cstep F X k P
  (* dtrans' <= t <= T f *)
  | ttrans : forall Q : cfg -> Prop,
      T cfg cstep F X k Q -> (forall k' : cfg, Q k' -> T cfg cstep F X k' P)
      -> T cfg cstep F X k P
  (* f (T f) <= (T f)(T f) <= T f *)
  | tfun' : forall (Q:Spec cfg),
              (forall k' P', Q k' P' -> T cfg cstep F X k' P') -> F Q k P -> T cfg cstep F X k P
  (* 1 <= T f *)
  | trule : X k P -> T cfg cstep F X k P
  (* sstep step (c -> d ...) *)
  | tstep : forall k' : cfg, cstep k k' -> T cfg cstep F X k' P -> T cfg cstep F X k P
  (* nu b <= t _|_ <= t X <= T f *)                                                         
  | tvalid : reaches cstep k P -> T cfg cstep F X k P.

Definition tfun : forall cfg cstep F X k P, F (T cfg cstep F X) k P -> T cfg cstep F X k P.
Proof. intros. eauto using tfun'. Defined.


Lemma hohoho : forall A x P, ho_spec (step kstep A) x P -> step kstep (T kcfg kstep ho_spec A) x P.
(* (forall A, ho_spec (step A) <= step (T ho_spec A))
 <-> ho_spec . step <= step . T ho_spec
  -> ho_spec <= B (T ho_spec)
  -> ho_spec <= t
 *)
Proof.
destruct 1.
destruct OddDef. simpl in H, H1. subst.
eapply sstep. step_solver.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
simpl.
split_bool (y =? 0);use_assumptions.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tdone. done_solver.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
simpl.
eapply ttrans.
match goal with [|-T kcfg kstep _ A ?c ?P] => assert (step kstep A c P) end.
eapply H0. simpl;equate_maps. assumption. pat_solver.
destruct H. apply tdone. assumption. eapply tstep. eassumption. clear H.
   apply trule. assumption.
trans_use_result.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
apply tdone.
done_solver.
rewrite Z.sub_1_r, Z.odd_pred. reflexivity.

(* Now odd *)

destruct EvenDef. simpl in H, H1. subst.
eapply sstep. step_solver.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
simpl.
split_bool (y =? 0);use_assumptions.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tdone. done_solver.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
simpl.
eapply ttrans.
match goal with [|-T kcfg kstep _ A ?c ?P] => assert (step kstep A c P) end.
eapply H0. simpl;equate_maps. assumption. pat_solver.
destruct H. apply tdone. assumption. eapply tstep. eassumption. clear H.   
   apply trule. assumption.
trans_use_result.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
apply tdone.
done_solver.
rewrite Z.sub_1_r, Z.even_pred. reflexivity.

(* even_final *)

simpl in H. eapply sstep. step_solver. 
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
simpl.
split_bool (y =? 0);use_assumptions.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tdone. done_solver.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
simpl. eapply ttrans.
eapply tfun. 
eapply odd_claim with (EvenDef := evenDef). reflexivity.
eapply z_spec_mono with (ho_spec A). apply even_final. 
intros. eapply tfun. apply my_ho_spec_mono. econstructor;[|eassumption].
intros. eapply trule. trivial.
step_solver.
assumption. done_solver. 
trans_use_result.
eapply tstep;[step_solver|].
eapply tstep;[step_solver|].
eapply tdone. done_solver.
rewrite Z.sub_1_r, Z.odd_pred. reflexivity.
Qed.

Inductive ho_spec_new : Spec kcfg :=
| even_new :
    z_spec Z.even (ho_spec_new) [oddDef] evenDef
| odd_new :
    z_spec Z.odd (ho_spec_new) [evenDef] oddDef
.

Theorem ho_spec_sound : sound kstep ho_spec_new.
Proof.
  apply proved_sound. intros. destruct H. simpl in H. eapply sstep. step_solver.
  eapply dtrans.
  (* step_solver. trans_tac.
  constructor. eapply sstep. 
  list_solver. eapply dtrans. simpl. econstructor. 
  constructor. *)
  Admitted.


