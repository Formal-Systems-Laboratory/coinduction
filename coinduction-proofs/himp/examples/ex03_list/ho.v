Require Import list_examples.
Require Import step_ok.

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
      z_spec Z.odd (ho_spec A) [EvenDef] oddDef.

Inductive nonho_spec : Spec kcfg :=
| even_final :
    z_spec Z.even nonho_spec [oddDef] evenDef
| odd_final :
    z_spec Z.odd nonho_spec [evenDef] oddDef.

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

(*Lemma ho_spec_mono :*)

Lemma ho_gfp : subspec (nonho_spec) (ho_spec nonho_spec).
Proof.
  destruct 1.
  eapply even_claim with (OddDef := oddDef); try eauto. apply odd_final.
  eapply odd_claim with (EvenDef := evenDef); try eauto. apply even_final. 
Qed.
  
Lemma ho_spec_mono : mono ho_spec.
Proof.
  destruct 2; econstructor; try(eapply z_spec_mono; eassumption; apply H); eassumption.
Qed. 

Lemma ho_ok : sound kstep nonho_spec.
Proof.
  unfold sound. apply ok with ho_spec. apply ho_spec_mono.
  intros. 
  destruct 1. destruct OddDef. simpl in H, H1. 
  eapply sstep. step_solver.
  do 6 (eapply tstep; try apply ho_spec_mono; try step_solver). 
  simpl.
  split_bool (y =? 0);use_assumptions.
  do 2 (eapply tstep; try apply ho_spec_mono; try step_solver). 
  eapply tdone; try apply ho_spec_mono; done_solver.
  do 8 (eapply tstep; try apply ho_spec_mono; try step_solver). 
  simpl.
  eapply ttrans; try apply ho_spec_mono.

  eapply z_spec_mono with (spec2 := T (step kstep) ho_spec A) in H0. eapply H0.
  simpl;equate_maps. assumption. pat_solver.
  intros. eapply Tf_id. trivial.
  trans_use_result.
  do 2 (eapply tstep; try apply ho_spec_mono; try step_solver).
  eapply tdone. apply ho_spec_mono. done_solver.
  rewrite Z.sub_1_r, Z.odd_pred. trivial.

  (* Now odd *)

  destruct EvenDef. simpl in H, H1. 
  eapply sstep. step_solver.
  do 6 (eapply tstep; try apply ho_spec_mono; try step_solver).
  simpl.
  split_bool (y =? 0);use_assumptions.
  do 2 (eapply tstep; try apply ho_spec_mono; try step_solver).
  eapply tdone; try apply ho_spec_mono; done_solver.
  do 8 (eapply tstep; try apply ho_spec_mono; try step_solver).
  simpl.
  eapply ttrans; try apply ho_spec_mono.

  eapply z_spec_mono in H0.
  eapply H0.
  simpl;equate_maps. assumption. pat_solver.
  intros. eapply Tf_id. trivial.
  trans_use_result.
  do 2 (eapply tstep; try apply ho_spec_mono; try step_solver).
  eapply tdone. apply ho_spec_mono. done_solver.
  rewrite Z.sub_1_r, Z.even_pred. trivial.

  apply ho_gfp.
Qed.

(* Print Assumptions ho_ok. *)

