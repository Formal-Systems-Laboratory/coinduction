Require Import kstyle.
Require Import ZArith.
Require Import domains.
Require Import evaluator.

(* from Software Foundations *)
Require Import Ascii String.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) → let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c → let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "fun b c → Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".

Extract Inductive sumbool => "bool" ["true" "false"].

(*
These definitions are enough to extract Z with int (should be big_int) and run eval,
but the generated eval.ml and eval.mli still include many other definitions in Z and positive
that want the induction principle, and have to be removed by hand before it runs

Extract Inductive positive => "int" ["(fun n -> 2 * n + 1)" "(fun n -> 2 * n)" "1"] "induction on positive!".
Extract Inductive Z => "int" ["0" "(~+)" "(~-)"] "induction on Z!".
Extract Inlined Constant Zplus => "(+)".
Extract Inlined Constant Zminus => "(-)".
Extract Inlined Constant Zdiv => "(/)".
Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Zneq_bool => "(!=)".
*)

Definition testcfg :=
  (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" |-> 1000000%Z) mapEmpty mapEmpty).

Extraction "himp/eval.ml" eval testcfg.

(*
let rec run cfg = match eval cfg with
  | None -> cfg
  | Some cfg' -> run cfg'
*)
