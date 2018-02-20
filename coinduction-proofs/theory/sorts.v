Require Vector.
Require Import Relation_Operators.
Require Import List.

Set Implicit Arguments.

(*
  Defining terms over order-sorted labels, including
  subsorting, overloading, and associativity as in K.
  This is a step towards allowing a deep embedding of
  K definitions.
 *)

Inductive Sorts := MkSorts {
  num_sorts : nat;
  sort : Set := Fin.t num_sorts;
  subsorts : list (sort * sort)
  }.

Print Relation_Definitions.
Definition subsort (s:Sorts) : sort s -> sort s -> Prop :=
  clos_refl_trans _ (fun a b => In (a,b) (subsorts s)).


Inductive SortModel (s : Sorts) : Type := MkSortModel
  { sort_impls : Vector.t Set (num_sorts s)
  ; sort_impl : sort s -> Set := Vector.nth sort_impls
  ; inj_impl : forall (s1 s2 : sort s) (H : subsort s1 s2),
      Vector.nth sort_impls s1 -> Vector.nth sort_impls s2
  ; inj_coh : forall (s1 s2 s3 : sort s) H12 H23 H13 x,
      @inj_impl s2 s3 H23 (@inj_impl s1 s2 H12 x) = @inj_impl s1 s3 H13 x
  }.

Inductive LabelDef (s : Sorts) := MkLabelDef {
  arity : nat;
  sigs : list (sort s * Vector.t (sort s) arity)
  }.

Inductive Labels := MkLabels {
  sorts : Sorts ;
  labels : list (LabelDef sorts)
  }.

Fixpoint fin_ix {A : Type} (l : list A) (ix : Fin.t (length l)) : A :=
  match l return Fin.t (length l) -> A with
    | (x :: l') => fun ix => match ix in Fin.t n return n = S (length l') -> A with
       | Fin.F1 _ => fun _ => x
       | Fin.FS _ ix' => fun H => fin_ix l' (eq_rec _ Fin.t ix' _ (eq_add_S _ _ H))
       end (eq_refl _)
    | nil => fun ix => match ix with end
  end ix.

Inductive LabelInstance (l : Labels) : Set :=
  MkLabelInstance { label_ix : Fin.t (length (labels l))
          ; label_def := fin_ix _ label_ix
          ; li_arity := arity label_def
          ; sig_ix : Fin.t (length (sigs label_def))
          ; li_sig := fin_ix _ sig_ix
          }.

Inductive term (l : Labels) (Var : sort (sorts l) -> Set) : sort (sorts l) -> Set :=
 |var : forall s1 s2, subsort s1 s2 -> Var s1 -> term l Var s2
 |app : forall (li : LabelInstance l) s,
     subsort (fst (li_sig li)) s ->
     terms _ Var (snd (li_sig li)) -> term _ Var s
with terms (l : Labels) (Var : sort (sorts l) -> Set) : forall n, Vector.t (sort (sorts l)) n -> Set :=
  | terms_nil : terms l Var (@Vector.nil _)
  | terms_cons : forall s, term l Var s ->
     forall n ss, terms l Var ss -> terms l Var (Vector.cons _ s n ss)
  .

Arguments rt_trans [A R x y z] _ _.

Definition inj {l V s1 s2} (H : subsort s1 s2) (t : term l V s1) : term l V s2 :=
  match t in term _ _ s return subsort s s2 -> term l V s2 with
    | var s0 s H0 v => fun H' => @var l V s0 s2 (rt_trans H0 H') v
    | app li s H0 ts => fun H' => @app l V li s2 (rt_trans H0 H') ts
  end H.

Definition VProp {A} n : Vector.t A n -> Prop :=
  match n return Vector.t A n -> Prop with
  | 0 => fun _ => True
  | S _ => fun v => v = Vector.cons _ (Vector.hd v) _ (Vector.tl v)
  end.

Lemma Vector_ht : forall A n (v : Vector.t A (S n)),
   v = Vector.cons _ (Vector.hd v) _ (Vector.tl v).
Proof. intros. change (VProp v). destruct v;reflexivity. Qed.

Fixpoint injs {l V n ss1} (ts : @terms l V n ss1) :
   forall ss2, Vector.Forall2 (@subsort _) ss1 ss2 -> terms l V ss2.
refine (match ts in @terms _ _ n ss return
    forall ss2, Vector.Forall2 (@subsort _) ss ss2 -> terms l V ss2 with
  | terms_cons s t n' ss ts' => fun ss2 H => _
  | terms_nil => fun ss2 H =>
      match ss2 in Vector.t _ n return match n with 0 => terms l V ss2 | S _ => unit end with
      | Vector.nil => terms_nil _ _
      | Vector.cons _ _ _ => tt
      end
  end).
clear n ts ss1.
intros. rewrite (Vector_ht ss2) in H |- *.
refine (terms_cons (inj _ t) (injs l _ _ _ ts' _ _)).
inversion H. assumption.
inversion H.
apply Eqdep_dec.inj_pair2_eq_dec in H5.
apply Eqdep_dec.inj_pair2_eq_dec in H2.
subst.
assumption.
exact Peano_dec.eq_nat_dec.
exact Peano_dec.eq_nat_dec.
Defined.

Inductive term_equiv l V : forall s, term l V s -> term l V s -> Prop :=
 | te_refl : forall s t, @term_equiv l V s t t
 | te_sym : forall s t t', @term_equiv l V s t t' -> term_equiv t' t
 | te_trans : forall s t1 t2 t3, @term_equiv l V s t1 t2 -> term_equiv t2 t3
     -> term_equiv t1 t3
 | te_cong : forall li s H H' ts ts',
     terms_equiv ts ts' ->
     term_equiv (@app _ _ li s H ts) (app li H' ts')
 | te_overload : forall (lix : Fin.t (length (labels l))),
     let label_def := fin_ix _ lix in
     forall (s1 s2 : Fin.t (length (sigs label_def))), 
     forall s (H1 : subsort (fst (fin_ix _ s1)) s) (H2 : subsort (fst (fin_ix _ s2)) s),
       forall ss (HS1 : Vector.Forall2 (@subsort _) ss (snd (fin_ix _ s1)))
                 (HS2 : Vector.Forall2 (@subsort _) ss (snd (fin_ix _ s2))),
     forall (ts : terms l V ss),
       term_equiv (app (MkLabelInstance l lix s1) H1 (injs ts HS1))
                  (app (MkLabelInstance l lix s2) H2 (injs ts HS2))
with terms_equiv l V : forall n ss, @terms l V n ss -> terms l V ss -> Prop :=
 | terms_equiv_nil : terms_equiv (terms_nil l V) (terms_nil l V)
 | terms_equiv_cons : forall s t t', @term_equiv _ _ s t t' ->
    forall n ss ts ts', @terms_equiv _ _ n ss ts ts'
     -> terms_equiv (terms_cons t ts) (terms_cons t' ts')
 .

Definition sig_impl {A:Set} (El : A -> Set) {n} (sig : (A * Vector.t A n)) : Set :=
  (fix args n (codes : Vector.t A n) :=
  match codes with
    | Vector.nil => El (fst sig)
    | Vector.cons c _ cs => El c -> args _ cs
  end) _ (snd sig).

Fixpoint eval_term l
  (sorts_model : SortModel (sorts l))
  (label_impl : forall (li : LabelInstance l),
      sig_impl (sort_impl sorts_model) (li_sig li))
  (V : sort (sorts l) -> Set)
  (var_impl : forall s, V s -> sort_impl sorts_model s)
  s (t : term l V s) : sort_impl sorts_model s :=
  match t with
  | var s1 s2 H v => inj_impl sorts_model H (var_impl _ v)
  | app li s H ts  => inj_impl sorts_model H
       (eval_terms sorts_model label_impl var_impl ts _ (label_impl li))
  end
with eval_terms l
  (sorts_model : SortModel (sorts l))
  (label_impl : forall (li : LabelInstance l),
      sig_impl (sort_impl sorts_model) (li_sig li))
  (V : sort (sorts l) -> Set)
  (var_impl : forall s, V s -> sort_impl sorts_model s)
  n ss (ts : @terms l V n ss) :
    forall s, sig_impl (sort_impl sorts_model) (s,ss) -> sort_impl sorts_model s :=
  match ts in terms _ _ ss return forall s : sort (sorts l),
   sig_impl (sort_impl sorts_model) (s, ss) -> sort_impl sorts_model s with
  | terms_nil => fun _ R => R
  | terms_cons _ t _ _ ts' => fun _ F =>
     (eval_terms sorts_model label_impl var_impl ts' _
        (F (eval_term _ label_impl var_impl t)))
  end.

Inductive LabelsModel (l : Labels) : Type := MkLabelsModel
  { sorts_model : SortModel (sorts l)
  ; label_impl : forall (li : LabelInstance l),
      sig_impl (sort_impl sorts_model) (li_sig li)
  ; eval : forall (V : sort (sorts l) -> Set)
                  (V_impl : forall s, V s -> sort_impl sorts_model s)
                  s, term l V s -> sort_impl sorts_model s
      := eval_term sorts_model label_impl
  ; label_coh : forall (V : sort (sorts l) -> Set)
                       (V_impl : forall s, V s -> sort_impl sorts_model s)
       s t1 t2, @term_equiv l V s t1 t2 -> eval V_impl t1 = eval V_impl t2
  }.

Extraction Implicit Fin.F1 [1].
Extraction Implicit Fin.FS [1].
Extraction Implicit Vector.cons [n].
Extraction Implicit Vector.hd [n].
Extraction Implicit Vector.tl [n].
Extraction Implicit terms_cons [s n ss].
Extraction Implicit inj [l s1].
Extraction Implicit injs [l n ss1].
Recursive Extraction injs.
