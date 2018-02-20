Require Import list_examples.

Definition reverse_def := FunDef "reverse" ["x"]
 {{Decl "p";Decl "y"; "p"<-0
  ;SWhile ("x"<>0)
    {{"y"<-arr_next "x"
     ;"x"<<-build_node (arr_val "x") (EVar "p")
     ;"p"<-"x"
     ;"x"<-"y"}}
  ;SReturn "p"}}.

Inductive reverse_spec : Spec kcfg :=
  reverse_claim : forall l x, heap_fun reverse_spec nil
  reverse_def [Int x] (rep_list l x) (rep_list (rev l))
 (* <k>reverse(X) => ?R...</k>
    <heap>... list(L,X) => list(rev(L),?R) ...</heap> *)
 |loop_claim : forall A B x p v, heap_loop reverse_spec
  reverse_def 0 ("x" s|-> KInt x :* "p" s|-> KInt p :* "y" s|-> v)
    (rep_list A x :* rep_list B p) (rep_list (rev_append A B))
 (* <k>while(...){...} => return ?R ...</k>
    <env>"x" |-> X, "p" |-> P, "y" |-> _ => _</env>
    <heap>... list(A,X),list(B,P) => list(rev_append(A,B),?R) ...</heap> *).

Lemma reverse_proof : sound kstep reverse_spec.
Proof. list_solver.
rewrite <- rev_alt in * |- .
list_run. Qed.