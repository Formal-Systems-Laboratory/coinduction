Require Import maps.
Require Import String.
Require Import List.
Require Import NPeano.

Set Implicit Arguments.

(* Working towards a proof-by-reflection version of equate_maps, compare maps.v

   For now, importing this module replaces the normalization in maps.v
 *)

Fixpoint merge {A} (le : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l1 with
    | nil => l2
    | (cons v1 l1') =>
      (fix scan l2 :=
         match l2 with
           | nil => l1
           | cons v2 l2' =>
             if le v1 v2
             then cons v1 (merge le l1' l2)
             else cons v2 (scan l2')
         end) l2
  end.
Arguments merge A le !l1 !l2.

Definition mergeTest
 : merge NPeano.ltb (cons 1 (cons 3 (cons 4 nil))) (cons 0 (cons 2 (cons 5 nil)))
 = cons 0 (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))
 := eq_refl _.

(* Map representation and interpretation *)
Section MapRep.
  Variables Key Val : Type.

Inductive item_rep : Type :=
  | item (k : nat) (v : Val)
  | submap (m : nat)
  | evar (e : Map Key Val)
  .
Inductive map_rep : Type :=
  | empty
  | join (l r : map_rep)
  | atom (a : item_rep)
  .

Definition interp_item keys submaps (i : item_rep) : Map Key Val :=
  match i with
    | item k v =>
      match nth_error keys k with
        | Some k => k |-> v
        | None => mapEmpty
      end
    | submap m =>
      match nth_error submaps m with
        | Some m => m
        | _ => mapEmpty
      end
    | evar e => e
  end.

Definition interp keys submaps : map_rep -> Map Key Val :=
  fix eval m := match m with
    | empty => mapEmpty
    | join l r => eval l :* eval r
    | atom a => interp_item keys submaps a
  end.

Definition mapEq keys submaps ml mr : Prop :=
     interp keys submaps ml
  ~= interp keys submaps mr.

Definition item_le (i1 i2 : item_rep) : bool :=
  match i1, i2 with
    | item k v, item k2 v2 => leb k k2
    | item _ _, _ => true
    | submap _, item _ _ => false
    | submap m, submap m2 => leb m m2
    | submap _, _ => true
    | evar _, evar _ => true
    | evar _, _ => false
  end.

(* Drop empties, and sort things into the order we want *)
Fixpoint canonicalize (m : map_rep) : list item_rep :=
  match m with
    | empty => nil
    | join l r => merge item_le (canonicalize l) (canonicalize r)
    | atom a => cons a nil
  end.

Definition joins (l : list map_rep) :=
  match l with
    | nil => empty
    | r :: nil => r
    | _ => fold_right join empty l
  end.
Arguments joins l : simpl never.

Fixpoint joins2 (l : list map_rep) :=
  match l with
    | nil => empty
    | r :: nil => r
    | r :: rs => join r (joins2 rs)
  end.
  Functional Scheme joins2_ind := Induction for joins2 Sort Prop.

  Section Equivalence.
  Variable keys : list Key.
  Variable submaps : list (Map Key Val).

  Local Notation int := (interp keys submaps).

  Lemma merge_ {A} (lt : A -> A -> bool) (f : A -> map_rep) (l1 l2 : list A) :
    int (fold_right join empty (map f (merge lt l1 l2)))
        ~= int (join (fold_right join empty (map f l1))
               (fold_right join empty (map f l2))).
  revert l2; induction l1; intro.
  simpl; rewrite equivUnitL; reflexivity.

  induction l2.
  simpl;rewrite equivUnit;reflexivity.
  simpl;destruct (lt a a0);
  simpl;rewrite ?IHl1,?IHl2;simpl;equate_maps.
  Qed.

  Lemma joins_joins2 l : int (fold_right join empty l) ~= int (joins2 l).
  Proof.
    functional induction (joins2 l).
    reflexivity.
    apply equivUnit.
    simpl;rewrite IHm;reflexivity.
  Qed.

  Lemma canon_equiv : forall m, int m ~= int (fold_right join empty (map atom (canonicalize m))).
  Proof.
    induction m;simpl;rewrite ?equivUnit, ?equivUnitL; try reflexivity.
    rewrite IHm1, IHm2, merge_. reflexivity.
  Qed.

  Lemma map_simplify: forall m1 m2,
    int (joins2 (map atom (canonicalize m1))) ~= int (joins2 (map atom (canonicalize m2)))
    -> int m1 ~= int m2.
  intros. rewrite canon_equiv, joins_joins2, H, <- joins_joins2, <- canon_equiv. reflexivity.
  Qed.
  End Equivalence.
End MapRep.

Ltac inList x xs :=
  match xs with
      | nil => false
      | x :: _ => true
      | _ :: ?xs' => inList x xs'
  end.
Ltac insert x xs :=
  match inList x xs with
    | true => xs
    | false => constr:(x :: xs)
  end.
Ltac index x xs :=
  match xs with
    | (x :: _) => constr:0
    | (?x' :: ?xs) => let ix := index x xs in constr:(S ix)
  end.
Ltac gatherKeys gathered t :=
  match t with
    | ?l :* ?r => let gathered' := gatherKeys gathered l in gatherKeys gathered' r
    | (?k |-> _) => insert k gathered
    | _ => gathered
  end.
Ltac gatherSubmaps gathered t k :=
  match t with
    | ?l :* ?r =>
      gatherSubmaps gathered l ltac:(fun gathered' =>
      gatherSubmaps gathered' r k)
    | (_ |-> _) => k gathered
    | ?m =>
      first [is_evar m; k gathered
            | let gathered' := insert m gathered in k gathered'
            ]
  end.

Ltac quoteMap K V keys maps t k :=
  match t with
    | (@mapEmpty _ _) => let rep := constr:(empty K V) in k rep
    | ?l :* ?r =>
      quoteMap K V keys maps l ltac:(fun repl =>
      quoteMap K V keys maps r ltac:(fun repr =>
      let rep := constr:(join repl repr) in k rep
      ))
    | ?key |-> ?v =>
      let repk := index key keys in
      let rep := constr:(atom (item K repk v))
      in k rep
    | ?m =>
      first [is_evar m;
             let rep := constr:(atom (evar m))
             in k rep
            |let repm := index m maps in
             let rep := constr:(atom (submap K V repm))
             in k rep]
  end.
Ltac quote_map_equation := match goal with
    [|- @MapEquiv ?K ?V ?l ?r ] =>
    let ks := gatherKeys (@nil K) l in
    let ks := gatherKeys ks r in
    gatherSubmaps (@nil (Map K V)) l ltac:(fun ms =>
    gatherSubmaps ms r ltac:(fun ms =>
    quoteMap K V ks ms l ltac:(fun repl =>
    quoteMap K V ks ms r ltac:(fun repr =>
      change (interp ks ms repl ~= interp ks ms repr)))))
end.

Definition quote_test0
  : forall (k1 : string) (v1 : nat),
    k1 |-> v1 ~= k1 |-> v1.
Proof.
intros.
quote_map_equation.
reflexivity.
Qed.

Definition quote_test1
  : forall (m : Map string nat),
    m ~= m.
Proof.
intros.
quote_map_equation.
reflexivity.
Qed.

Definition quote_test2
  : forall (m : Map string nat), exists m2, m ~= m2.
Proof.
intros.
eexists.
quote_map_equation.
simpl.
reflexivity.
Qed.

Definition simplify_test1
  : forall (k1 k2 : string) (v1 v2 : nat) (m1 : Map string nat),
    exists m1',
    exists v2',
    k1 |-> v1 :* m1 :* k2 |-> v2 ~= m1' :* k2 |-> v2' :* k1 |-> v1.
Proof.
intros.
eexists.
eexists.
quote_map_equation.
apply map_simplify.
simpl joins2.
simpl interp.
reflexivity.
Qed.

Ltac canonicalize_maps := quote_map_equation;apply map_simplify;simpl interp.

Ltac prepare_maps ::=
  match goal with
    | [|- ?l ~= ?r] => expand_map l;expand_map r
  end;
  canonicalize_maps;
  (* switch if left side has a map evar *)
  match goal with
    | [|- ?l ~= ?r] =>
        match l with
          | context [?v] => is_evar v;
            match type of v with Map _ _  => symmetry end
        end
    | _ => idtac
  end
  .

(*
Fixpoint removeMatches' {A} (cmp : A -> A -> comparison) (l1 l2 l1_acc l2_acc : list A) : (list A * list A) :=
  match l1 with
    | nil => (rev l1_acc, rev_append l2_acc l2)
    | (cons v1 l1') =>
      (fix scan l2 l2_acc {struct l2} :=
         match l2 with
           | nil => (rev_append l1_acc l1, rev l2_acc)
           | cons v2 l2' =>
             match cmp v1 v2 with
               | Lt => removeMatches' cmp l1' l2 (v1::l1_acc) l2_acc
               | Eq => removeMatches' cmp l1' l2' l1_acc l2_acc
               | Gt => scan l2' (v2::l2_acc)
             end
         end) l2 l2_acc
  end.

Definition removeMatches {A} cmp (l1 l2 : list A) := removeMatches' cmp l1 l2 nil nil.

Fixpoint removeMatches'' {A} (cmp : A -> A -> comparison)
         (l1 l2 : list A) eq_acc (l1_acc l2_acc : list A)
  : (list (A * A) * list A * list A) :=
  match l1 with
    | nil => (rev eq_acc, rev l1_acc, rev_append l2_acc l2)
    | (cons v1 l1') =>
      (fix scan l2 eq_acc l2_acc {struct l2} :=
         match l2 with
           | nil => (rev eq_acc, rev_append l1_acc l1, rev l2_acc)
           | cons v2 l2' =>
             match cmp v1 v2 with
               | Lt => removeMatches'' cmp l1' l2 eq_acc (v1::l1_acc) l2_acc
               | Eq => removeMatches'' cmp l1' l2' ((v1,v2)::eq_acc) l1_acc l2_acc
               | Gt => scan l2' eq_acc (v2::l2_acc)
             end
         end) l2 eq_acc l2_acc
  end.

Definition test2 :
  removeMatches Nat.compare (cons 1 (cons 3 (cons 4 nil))) (cons 0 (cons 1 (cons 2 (cons 4 nil))))
  = (cons 3 nil, cons 0 (cons 2 nil)) := eq_refl _.

Definition item_cmp (i1 i2 : item_rep) : comparison :=
  match i1, i2 with
    | item k v, item k2 v2 =>
      match Nat.compare k k2 with
        | Eq => Nat.compare v v2
        | o => o
      end
    | item _ _, submap _ => Lt
    | submap _, item _ _ => Gt
    | submap m, submap m2 => Nat.compare m m2
  end.

Lemma item_cmp_prop : forall i1 i2, item_cmp i1 i2 = Eq -> i1 = i2.
Proof.
destruct i1;destruct i2;simpl;unfold Nat.compare;
repeat match goal with [|-context [Compare_dec.nat_compare ?x ?y]] =>
                   destruct (Compare_dec.nat_compare_spec x y) end;
congruence.
Qed.


  Section RemoveEquiv.
    Variable m1 m2 : map_rep. (* Need a rest of map to make this flexible enough *)

  Local Notation build_equiv l1 l2 := (int (joins (m1 :: map atom l1)) ~= int (joins (m2 :: map atom l2))).

  Lemma app_equiv l1 l2 : int (joins (l1 ++ l2)) ~= int (joins l1) :* int (joins l2).
    induction l1.
    simpl; rewrite equivUnitL; reflexivity.
    simpl app. rewrite !joins_cons.
    rewrite IHl1, equivAssoc; reflexivity.
  Qed.

  Lemma removeEquivSubmaps (l1 l2 l1_acc l2_acc : list item_rep) :
    match removeMatches' item_cmp l1 l2 l1_acc l2_acc with
      | (l1', l2') => build_equiv l1' l2'
    end ->
    build_equiv (rev_append l1_acc l1) (rev_append l2_acc l2).
  revert l1_acc l2 l2_acc;induction l1.
  simpl; intros; rewrite <- rev_alt; assumption.
  induction l2.
  simpl; intros; rewrite <- rev_alt; assumption.
  intros; simpl in * |- *. fold joins.
  destruct (item_cmp a a0) eqn:Hcmp.
  (* Both step? *)
  (* Eq -> goes back to outer IH, with thing dropped *)
  specialize (IHl1 _ _ _ H); clear -Hcmp IHl1.
    (* rearranging. *)
    apply item_cmp_prop in Hcmp. subst a.
    rewrite !rev_append_rev, !map_app, !joins_cons, !app_equiv in IHl1 |- *.
    simpl. rewrite !joins_cons.
    unfold interp;fold int.
    repeat rewrite (equivComAssoc _ (interp_item _ _ _ a0) _).
    rewrite IHl1. reflexivity.
  (* Lt -> use outer IH? *)
  apply IHl1 with (l1_acc := (a :: l1_acc)).
  assumption.
  (* Gt -> use inner IH *)
  apply (IHl2 (a0 :: l2_acc)).
  apply H.
  Qed.
  End RemoveEquiv.

  Lemma reduce_equiv (rep1 rep2 : map_rep) :
    match removeMatches item_cmp (canonicalize rep1) (canonicalize rep2) with
      | (items1, items2) =>
        int (joins (map atom items1)) ~= int (joins (map atom items2))
    end
    -> int rep1 ~= int rep2.
  Proof.
    unfold removeMatches; intros.
    rewrite (canon_equiv rep1), (canon_equiv rep2).
    setoid_rewrite <- equivUnitL.
    change mapEmpty with (int empty).
    rewrite <- 2! joins_cons.
    change (int (joins (empty :: map atom (rev_append nil (canonicalize rep1))))
         ~= int (joins (empty :: map atom (rev_append nil (canonicalize rep2))))).
    apply removeEquivSubmaps.
    destruct (removeMatches' item_cmp (canonicalize rep1)
         (canonicalize rep2) nil nil).
    rewrite 2! joins_cons, H;reflexivity.
  Qed.
End Equivalence.

Definition test3 : forall (k1 k2 : string) (v1 v2 : nat) (m1 : Map string nat),
                     k1 |-> v1 :* m1 :* k2 |-> v2 ~= m1 :* k2 |-> v2 :* k1 |-> v1.
Proof.
intros.
change
  (interp (k1 :: k2 :: nil) (v1 :: v2 ::nil) (m1 :: nil)
        (join (atom (item 0 0)) (join (atom (submap 0)) (atom (item 1 1))))
     ~=
  interp (k1 :: k2 :: nil) (v1 :: v2 ::nil) (m1 :: nil)
        (join (atom (submap 0)) (join (atom (item 1 1)) (atom (item 0 0))))).
apply reduce_equiv.
simpl.
reflexivity.
Qed.

Definition test4 : forall (k1 k2 : string) (v1 v2 : nat) (m1 : Map string nat),
                     k1 |-> v1 :* m1 :* k2 |-> v2 ~= m1 :* k2 |-> v2 :* k1 |-> v1.
Proof.
intros.
quote_map_equation.
apply reduce_equiv.
simpl.
reflexivity.
Qed.
*)
