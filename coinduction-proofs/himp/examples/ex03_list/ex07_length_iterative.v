Require Import list_examples.

Definition length_def := FunDef "length" ["x"]
 {{Decl "l";"l"<-0
  ;SWhile ("x"<>0) {{"l"<-"l"+1; "x"<- arr_next "x"}}
  ;SReturn "l"}}.

Inductive length_spec : Spec kcfg :=
  length_claim : forall H x l, heap_fun length_spec nil
  length_def [Int x]
    (asP H (rep_list l x))
    (fun r => constraint (r = zlength l) :* litP H)
 |loop_claim : forall H k x l, heap_loop length_spec
  length_def 0 ("x" s|-> KInt x :* "l" s|-> KInt k)
    (asP H (rep_list l x))
    (fun r => constraint (r = k + zlength l) :* litP H).

Lemma length_proof : sound kstep length_spec.
Proof. list_solver. Qed.