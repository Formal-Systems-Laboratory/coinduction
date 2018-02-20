Require Import list_examples.

(* Splitting the code into several definitions
   reduces proof time by reducing the size of
   terms at any single point in the proof *)
Definition delete_loop2 :=
  (SWhile (arr_next "y"<>0)
  (Seq ("z"<-arr_next "y")
       (SIf (arr_val "z"="v")
          (Seq ("y"<<-build_node (arr_val "y") (arr_next "z"))
               (HDealloc "z"))
          ("y"<-"z"))))%code.
Definition delete_tail1 :=
 {{SIf ("x"=0) (SReturn 0) Skip
  ;Decl "z"
  ;"y"<-"x"
  ;delete_loop2
  ;SReturn "x"}}%code.
Definition delete_def := FunDef "delete" ["x";"v"]
 (Seq (Decl "y")
 (Seq (SWhile (("x"<>0) && (arr_val "x"="v"))
   {{"y"<-arr_next "x";HDealloc "x";"x"<-"y"}})
   delete_tail1))%code.

Fixpoint delete (v : Z) (l : list Z) : list Z :=
  match l with
    | nil => nil
    | (x :: l') => if Z_eq_dec v x then delete v l'
                   else x :: delete v l'
  end.
Arguments delete v l : simpl nomatch.

Inductive delete_spec : Spec kcfg :=
  delete_claim : forall l x v, heap_fun delete_spec nil
  delete_def [Int x;Int v] (rep_list l x) (rep_list (delete v l))
 |loop1_claim : forall l x v y, heap_loop delete_spec
  delete_def 0 ("x" s|-> KInt x :* "v" s|-> KInt v :* "y" s|-> y)
    (rep_list l x) (rep_list (delete v l))
 |loop2_claim : forall v A x yv B y z, heap_loop delete_spec
  delete_def 1 ("x" s|-> KInt x :* "v" s|-> KInt v
             :* "y" s|-> KInt y :* "z" s|-> z)
    (rep_seg A y x :* constraint (y <> 0) :* existsP q,
     y h|-> list_node yv q :* constraint (yv <> v) :* rep_list B q)
    (rep_list (A++yv::delete v B)).

Lemma delete_eq : forall v l, delete v (v :: l) = delete v l.
Proof. unfold delete;intros;destruct (Z.eq_dec v v);congruence. Qed.
Lemma delete_ne : forall v z l, v<>z -> delete v (z::l) = z::delete v l.
Proof. unfold delete;intros;destruct (Z.eq_dec v z);congruence. Qed.

Lemma delete_proof : sound kstep delete_spec.
Proof. list_solver;
rewrite ?delete_eq, ?delete_ne by congruence;
try rewrite app_ass in * |-;
list_run. Qed.