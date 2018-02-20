(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 14: Concurrent Separation Logic
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Map CSLSets Setoid Classes.Morphisms.
Require Import Decidable Coq.Logic.Eqdep Coq.Logic.EqdepFacts Peano_dec Coq.omega.Omega.

Require Import ho_proof_until_gen.
Require Import until_ok.

Set Implicit Arguments.

(* Let's combine the subjects of the last two lectures, to let us prove
 * correctness of concurrent programs that do dynamic management of shared
 * memory. *)


(** * Shared notations and definitions; main material starts afterward. *)

Notation heap := (fmap nat nat).
Notation locks := (set nat).

(* Hint Extern 1 (_ <= _) => linear_arithmetic. *)
(* Hint Extern 1 (@eq nat _ _) => linear_arithmetic. *)

(* Ltac simp := repeat (simplify; subst; propositional; *)
(*                      try match goal with *)
(*                          | [ H : ex _ |- _ ] => invert H *)
(*                         end); try linear_arithmetic. *)


(** * A shared-memory concurrent language with loops *)

(* Let's work with a variant of the shared-memory concurrent language from last
 * time.  We add back in result types, loops, and dynamic memory allocation. *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Definition valueOf {A} (o : loop_outcome A) :=
  match o with
  | Done v => v
  | Again v => v
  end.

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Fail {result} : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc

| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Lock (a : nat) : cmd unit
| Unlock (a : nat) : cmd unit
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit

| Par (c1 c2 : cmd unit) : cmd unit.

(* The next span of definitions is copied from SeparationLogic.v.  Skip ahead to
 * the word "Finally" to see what's new. *)

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Fixpoint initialize (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => initialize h base numWords' $+ (base + numWords', 0)
  end.

Fixpoint deallocate (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => deallocate (h $- base) (base+1) numWords'
  end.

Inductive cfg (A : Set) : Type :=
  Cfg {hp:heap
      ;lcks:locks
      ;command:cmd A}.

Inductive cslstep : forall A, cfg A -> cfg A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h l h' l',
  cslstep (Cfg h l c1) (Cfg h' l' c1')
  -> cslstep (Cfg h l (Bind c1 c2)) (Cfg h' l' (Bind c1' c2))
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h l,
  cslstep (Cfg h l (Bind (Return v) c2)) (Cfg h l (c2 v))

| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h l,
  cslstep (Cfg h l (Loop init body)) (Cfg h l (o <- body init; match o with
                                                     | Done a => Return a
                                                     | Again a => Loop a body
                                                     end))

| StepRead : forall h l a v,
  h $? a = Some v
  -> cslstep (Cfg h l (Read a)) (Cfg h l (Return v))
| StepWrite : forall h l a v v',
  h $? a = Some v
  -> cslstep (Cfg h l (Write a v')) (Cfg (h $+ (a, v')) l (Return tt))
| StepAlloc : forall h l numWords a,
  a <> 0
  -> (forall i, i < numWords -> h $? (a + i) = None)
  -> cslstep (Cfg h l (Alloc numWords)) (Cfg (initialize h a numWords) l (Return a))
| StepFree : forall h l a numWords,
  cslstep (Cfg h l (Free a numWords)) (Cfg (deallocate h a numWords) l (Return tt))

| StepLock : forall h l a,
  ~a \in l
  -> cslstep (Cfg h l (Lock a)) (Cfg h (l \cup {a}) (Return tt))
| StepUnlock : forall h l a,
  a \in l
  -> cslstep (Cfg h l (Unlock a)) (Cfg h (l \setminus {a}) (Return tt))

| StepPar1 : forall h l c1 c2 h' l' c1',
  cslstep (Cfg h l c1) (Cfg h' l' c1')
  -> cslstep (Cfg h l (Par c1 c2)) (Cfg h' l' (Par c1' c2))
| StepPar2 : forall h l c1 c2 h' l' c2',
  cslstep (Cfg h l c2) (Cfg h' l' c2')
  -> cslstep (Cfg h l (Par c1 c2)) (Cfg h' l' (Par c1 c2')).


Infix "==n" := eq_nat_dec (no associativity, at level 50).

Example incrementer :=
for i := tt loop
  _ <- Lock 0;
  n <- Read 0;
  _ <- Write 0 (n);
  _ <- Unlock 0;
  if n ==n 0 then
    Fail
  else
    Return (Again tt)
done.

Example incrementer_par := incrementer || incrementer.

Definition hprop := heap -> Prop.
(* We add the locks to the mix. *)

Definition himp (p q : hprop) := forall h, p h -> q h.
Definition heq (p q : hprop) := forall h, p h <-> q h.

(* Lifting a pure proposition: it must hold, and the heap must be empty. *)
Definition lift (P : Prop) : hprop :=
  fun h => P /\ h = $0.

(* Separating conjunction, one of the two big ideas of separation logic.
 * When does [star p q] apply to [h]?  When [h] can be partitioned into two
 * subheaps [h1] and [h2], respectively compatible with [p] and [q].  See book
 * module [Map] for definitions of [split] and [disjoint]. *)
Definition star (p q : hprop) : hprop :=
  fun h => exists h1 h2, split h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

(* Existential quantification *)
Definition exis A (p : A -> hprop) : hprop :=
  fun h => exists x, p x h.

(* Convenient notations *)
Notation "[| P |]" := (lift P) : sep_scope.
Infix "*" := star : sep_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).

(* And now we prove some key algebraic properties, whose details aren't so
 * important.  The library automation uses these properties. *)

Lemma iff_two : forall A (P Q : A -> Prop),
  (forall x, P x <-> Q x)
  -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
Proof.
  firstorder.
Qed.

Definition ptsto (a v : nat) : heap -> Prop := fun h => h = $0 $+ (a, v).

(* Recall that each lock has an associated invariant.  This program only uses
 * lock 0, and here's its invariant: memory cell 0 holds a positive number. *)
Definition incrementer_inv := 
  (exists n, ptsto 0 n * [| n > 0 |])%sep.

Definition incrementer_inv' := 
  (exis (fun n => ptsto 0 n * [| n > 0 |]))%sep.

Definition inc_inv A : cfg A -> Prop :=
  fun cfg => forall h l c,
      cfg = (Cfg h l c) ->
      exists (x : nat) (h1 h2 : heap),
        split h h1 h2 /\ disjoint h1 h2 /\ ptsto 0 x h1 /\ [|x > 0|]%sep h2.


Inductive ho_spec (B : Spec (cfg unit)) : Spec (cfg unit) :=
| claim1 : forall h P n,
    h = $0 $+ (0, n) -> n > 0 -> 
    B (Cfg h {} (P || incrementer)) (fun _ c => inc_inv c) (fun _ => False) ->
    ho_spec B (Cfg (h $+ (0, n)) {} (P || incrementer))
            (fun _ c => inc_inv c) (fun _ => False).


Inductive nonho_spec : Spec (cfg unit) :=
| nonho_claim : forall h n,
    h = $0 $+ (0, n) -> n > 0 -> 
    nonho_spec (Cfg (h $+ (0, n)) {} (incrementer || incrementer))
               (fun _ c => inc_inv c) (fun _ => False).


Lemma ho_spec_mono : mono ho_spec.
Proof.
  destruct 2. econstructor; try eassumption. apply H. eassumption.
Qed.

Lemma ho_gfp : subspec nonho_spec (ho_spec nonho_spec).
Proof.
  destruct 1. econstructor; try eassumption. assert (h = (h $+ (0,n))).
  subst. maps_equal. rewrite H1. econstructor; try eassumption.
Qed.

Ltac injpair1 H H1 := inversion H;
                      (try repeat apply inj_pair2 in H1; subst).
Ltac injpair2 H H1 H2 := inversion H;
                         (try repeat apply inj_pair2 in H1;
                          try repeat apply inj_pair2 in H2; subst).
Ltac injpair3 H H1 H2 H3 := inversion H;
                            (try repeat apply inj_pair2 in H1; 
                             try repeat apply inj_pair2 in H2; 
                             try repeat apply inj_pair2 in H3; subst).
Ltac injpair4 H H1 H2 H3 H4 := inversion H;
                               (try repeat apply inj_pair2 in H1; 
                                try repeat apply inj_pair2 in H2; 
                                try repeat apply inj_pair2 in H3; 
                                try repeat apply inj_pair2 in H4; subst).

Lemma heap_eq : forall h n,
    h = $0 $+ (0, n) -> n > 0 ->
    exists (x : nat) (h1 h2 : heap),
      split (h $+ (0, n)) h1 h2 /\ disjoint h1 h2 /\ ptsto 0 x h1 /\ [|x > 0|]%sep h2.
Proof.
  intros.
  exists n. exists ($0 $+ (0,n)). exists (h $- 0).
  split. unfold split. subst. 
  maps_equal. rewrite lookup_join1.
  rewrite lookup_add_eq. rewrite lookup_add_eq. trivial. trivial. trivial.
  eapply lookup_Some_dom. apply lookup_add_eq. trivial. 
  
  rewrite lookup_add_ne. rewrite lookup_join2.
  rewrite lookup_remove_ne. trivial. omega.
  apply lookup_None_dom. rewrite lookup_add_ne. apply lookup_empty. omega. omega.

  split. unfold disjoint. intros. apply H1.
  destruct (($0 $+ (0, n)) $? a) eqn:H'.
  destruct ((h $- 0) $? a) eqn:H''.
  exfalso. apply lookup_split in H'. inversion H'. inversion H3.
  rewrite lookup_empty in H5. inversion H5. inversion H3; subst. inversion H3. 
  apply lookup_remove_eq with (m := $0 $+ (0, n)) in H. rewrite H'' in H. inversion H.
  exfalso. apply H2. trivial. trivial. 

  split. unfold ptsto. trivial. unfold lift. split. assumption.
  subst. maps_equal. destruct k. rewrite lookup_remove_eq. rewrite lookup_empty.
  trivial. trivial.
  rewrite lookup_remove_ne. rewrite lookup_add_ne. trivial. omega. omega.
Qed.

Ltac incsolve H := unfold inc_inv; intros; 
                  inversion H; subst;
                   apply heap_eq; auto.

Lemma ho_ok_one : sound (@cslstep unit) nonho_spec.
Proof.
  unfold sound. eapply ok with ho_spec. apply ho_spec_mono.
  intros.
  destruct 1. eapply sstep. apply StepPar2. constructor. incsolve H2.

  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. constructor. constructor. firstorder. incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. apply StepBindProceed. incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. constructor. constructor. apply lookup_add_eq. trivial.
  incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. apply StepBindProceed. incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. constructor. econstructor. apply lookup_add_eq. trivial.
  incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. apply StepBindProceed. incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. econstructor. constructor. firstorder. incsolve H2.
  eapply tstep. apply ho_spec_mono.
  apply StepPar2. constructor. apply StepBindProceed. incsolve H2.
  destruct (n ==n 0). apply tdone. apply ho_spec_mono. omega.

  eapply tstep. apply ho_spec_mono.
  apply StepPar2. apply StepBindProceed. incsolve H2.
  eapply ttrans. apply ho_spec_mono.
 
  assert (T (step (@cslstep unit)) ho_spec A
            {| hp := h; lcks := {}; command := P || incrementer |} 
            (fun _ c : cfg unit => inc_inv c) (fun _ : cfg unit => False)).
  apply Tf_id. trivial.

  assert (({} \cup {0}) \setminus {0} = {}). sets idtac.
  rewrite H3.  
  assert (h $+ (0,n) $+ (0,n) = h) by maps_equal.
  rewrite H4. apply H2. 
  intros. simpl in H2. inversion H2. apply ho_gfp. 
Qed.   

(* Print Assumptions ho_ok_one. *)

Lemma map_get : forall n (v : nat), ($0 $+ (0, n) $+ (0, n)) $? 0 = Some v -> n = v.
Proof.
  intros.
  assert (($0 $+ (0, n) $+ (0, n)) $? 0 = Some n).
  apply lookup_add_eq. trivial. rewrite H in H0. inversion H0. trivial.
Qed.

Require Import until_all_ok.

Lemma ho_ok_all : sound (@cslstep unit) nonho_spec.
Proof.
  unfold sound. eapply ok with ho_spec. apply ho_spec_mono.
  intros.
  destruct 1. apply sstep. econstructor.
  apply StepPar2. constructor.
  
  intros. unfold incrementer in H2.
  injpair1 H2 H8. admit. clear H2. 

  injpair3 H5 H6 H7 H10. 
  split. incsolve H.  

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. constructor. constructor. sets idtac.

  intros. injpair1 H H8. admit. clear H.
  
  injpair4 H4 H8 H9 H9 H12.
  injpair4 H3 H9 H10 H10 H13.
  injpair1 H6 H11.
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. apply StepBindProceed.

  intros. injpair1 H H12. admit. clear H.

  injpair4 H9 H12 H13 H13 H16.
  injpair4 H3 H13 H14 H14 H17. clear H18.
  injpair4 H8 H14 H15 H15 H18.
  inversion H11. do 2 (apply inj_pair2 in H16). apply inj_pair2 in H19; subst.  
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. constructor. constructor. eapply lookup_add_eq. trivial.

  intros. injpair1 H H16. admit. clear H. clear H7. 
  injpair4 H12 H15 H16 H16 H19.
  injpair4 H7 H16 H17 H17 H20.
  injpair1 H11 H18. 
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. apply StepBindProceed.

  intros. injpair1 H H19. admit. clear H.
  injpair4 H16 H19 H20 H20 H23.
  injpair4 H15 H20 H21 H21 H24.
  inversion H17. do 2 (apply inj_pair2 in H22). apply inj_pair2 in H25; subst.
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. constructor. econstructor. eapply lookup_add_eq. trivial.

  apply map_get in H13; subst. 
  intros. injpair1 H H21. admit. clear H.
  injpair4 H17 H21 H22 H22 H25.
  injpair4 H13 H22 H23 H23 H26.
  injpair1 H18 H25. 
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. apply StepBindProceed.

  intros. injpair1 H H25. admit. clear H.
  injpair4 H22 H25 H26 H26 H29.
  injpair4 H21 H26 H27 H27 H30.
  inversion H23. do 2 (apply inj_pair2 in H28). apply inj_pair2 in H31; subst.
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. econstructor. constructor. sets idtac. right.
  unfold List.In. left. trivial.

  intros. injpair1 H H28. admit. clear H.
  injpair4 H24 H28 H29 H29 H32.
  injpair4 H23 H29 H30 H30 H33.
  injpair1 H25 H31.
  split. incsolve H.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  constructor. apply StepBindProceed.

  intros. injpair1 H H32. admit. clear H.
  injpair4 H29 H32 H33 H33 H36.
  injpair4 H28 H33 H34 H34 H37.
  inversion H30. do 2 (apply inj_pair2 in H35). apply inj_pair2 in H38; subst.
  split. incsolve H. 

  destruct (v ==n 0). apply tdone. apply ho_spec_mono. omega.

  apply tstep. apply ho_spec_mono. econstructor. apply StepPar2.
  apply StepBindProceed.

  intros. injpair1 H H35. admit. clear H.
  injpair4 H31 H35 H36 H36 H39.
  inversion H30. do 2 (apply inj_pair2 in H37). apply inj_pair2 in H40; subst.
  split. incsolve H.
  
  eapply ttrans. apply ho_spec_mono.
  assert (T (step (@cslstep unit)) ho_spec A
            {| hp := $0 $+ (0, v); lcks := {}; command := P || incrementer |} 
            (fun _ c : cfg unit => inc_inv c) (fun _ : cfg unit => False)).
  apply Tf_id. assumption.
  assert ($0 $+ (0, v) = $0 $+ (0, v) $+ (0, v) $+ (0, v)) by maps_equal.
  assert (({} \cup {0}) \setminus {0} = {}). sets idtac.
  rewrite <- H2. rewrite H30. apply H.

  intros. inversion H. apply ho_gfp.
Qed.



(* Print Assumptions ho_ok_all. *)

