Require Import list_examples.

(* Splitting the code into several definitions
   reduces proof time by reducing the size of
   terms at any single point in the proof *)
Definition copy_loop :=
  SWhile ("iterx"<>0)
   {{"node"<-EAlloc
    ;"node"<<-build_node (arr_val "iterx") 0
    ;"itery"<<-build_node (arr_val "itery") "node"
    ;"iterx"<-arr_next "iterx"
    ;"itery"<-arr_next "itery"
    }}.
Definition copy_tail :=
 {{"y"<-EAlloc;"y"<<-build_node (arr_val "x") 0
  ;"iterx"<-arr_next "x"
  ;"itery"<-"y"
  ;copy_loop
  ;SReturn "y"}}%code.
Definition copy_def := FunDef "copy" ["x"]
 {{Decl "y";Decl "iterx";Decl "itery";Decl "node"
  ;SIf ("x"=0) (SReturn 0) copy_tail}}.

Inductive copy_spec : Spec kcfg :=
  copy_claim : forall H l x, heap_fun copy_spec nil
  copy_def [Int x]
    (asP H (rep_list l x))
    (fun r => rep_list l r :* litP H)
 |loop_claim : forall x n A y v itery H B iterx,
  heap_loop copy_spec copy_def 0
      ("x" s|-> x :* "node" s|-> n :* "y" s|-> KInt y
      :* "iterx" s|-> KInt iterx :* "itery" s|-> KInt itery)
    (constraint (itery <> 0) :* rep_seg A itery y
     :* itery h|-> list_node v 0 :* asP H (rep_list B iterx))
    (fun r => rep_list (A ++ v :: B) r :* litP H).

Lemma copy_proof : sound kstep copy_spec.
Proof. list_solver.
rewrite app_ass in * |- .
list_run. Qed.

