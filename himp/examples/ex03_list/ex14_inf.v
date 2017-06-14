Require Import list_examples.

Definition heap_fun' (R : Spec kcfg) (deps : list Defn) (d:Defn) (y : Exp) :
  forall (args : list KResult) (init_heap : MapPattern k k)
    (ret : Z -> MapPattern k k), Prop :=
  match d with FunDef name formals body =>
    fun args init_heap ret =>
      forall krest store stack heap funs mark otherfuns,
      funs ~= fundefs deps (name s|-> KDefn d) :* otherfuns ->
      (mark > 0)%Z ->
      forall frame,
      heap |= (init_heap :* litP frame) ->
      R (KCfg (kra (ECall name (map KResultToExp args) + y)%code krest)
              store stack heap funs mark)
        (fun _ => False)
  end.


(* Nonterminating program. Note loading the value "x" has the potential to get
   stuck but the program will not reach that point *)

Definition inf_rec := FunDef "sum_recursive_inf" ["x"]
 (SIf (BCon false)
   (SReturn 0)
   (SReturn (ECall "sum_recursive_inf" [ECon 1] + arr_val "x"))).

Inductive inf_rec_spec : Spec kcfg :=
  rec_claim : forall H x' x, heap_fun' inf_rec_spec nil inf_rec x' [Int x]
    H
    (fun r => constraint False).

Lemma inf_rec_proof : sound kstep inf_rec_spec.
Proof.
  apply proved_sound. intros. inversion H. simpl in H4. subst. simpl.
  eapply sstep. step_solver. 
  eapply dstep. step_solver. 
  eapply dstep. step_solver.
  eapply dstep. step_solver.
  eapply dtrans.
  econstructor. trans_solver. assumption. eassumption. trans_solver.
Qed.


(* Trivial nonterminating iterative program. Analogous iterative program as
   above gets stuck loading array value and thus is terminating *)

Definition inf_it := FunDef "sum_inf" ["x"]
 {{Decl "s";"s"<-0
  ;SWhile (BCon true) {{"s"<-"s"+1}}
  ;SReturn "s"}}.

Inductive inf_it_spec : Spec kcfg :=
  inf_claim : forall k H l x, heap_loop inf_it_spec
  inf_it 0 ("s" s|-> KInt k :* "x" s|-> KInt x)
    (asP H (rep_list l x))
    (fun r => constraint False).

Lemma inf_it_proof : sound kstep inf_it_spec.
Proof. list_solver. Qed.
