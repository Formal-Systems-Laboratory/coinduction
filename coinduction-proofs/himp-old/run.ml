open Eval

(* Conversion from Coq-style integers.
   Comment these and uncomment the trivial versions below
   when extracting Z as int
*)
let rec nat_to_pos = function
    1 -> XH
  | n -> if n land 1 = 1 then XI (nat_to_pos (n lsr 1)) else XO (nat_to_pos (n lsr 1))

let rec pos_to_nat = function
    XH -> 1
  | XI p -> 1 + pos_to_nat p lsl 1
  | XO p -> pos_to_nat p lsl 1

let int_to_z n =
  if n > 0 then Zpos (nat_to_pos n)
  else if n < 0 then Zneg (nat_to_pos (- n))
  else Z0

let z_to_int = function
    Zpos p -> pos_to_nat p
  | Zneg p -> - pos_to_nat p
  | Z0 -> 0

(*
let int_to_z n = n
let z_to_int z = z
*)

let rec run cfg = match eval cfg with
  | Some cfg' -> run cfg'
  | None -> cfg

let _ = run testcfg

let n_testcfg n =
  { kcell =
    (kra (KStmt (SWhile ((BLe ((ECon (int_to_z 0)), (EVar (String ('x',
      EmptyString))))), (SAssign ((String ('x', EmptyString)), (EPlus ((EVar
      (String ('x', EmptyString))), (ECon (int_to_z (-1)))))))))) Nil); store =
    (MapItem ((String ('x', EmptyString)), int_to_z n));
    heap = MapEmpty; labels = MapEmpty }

let print_z z = print_int (z_to_int z)

let rec print_estr = function
  String (c,s) -> print_char c; print_estr s
  | EmptyString -> ()

let print_map print_elt m = let rec print = function
    MapItem (s, v) -> print_estr s; print_string " |-> "; print_elt v
  | MapJoin (m1, m2) -> print m1; print_string " , " ; print m2
  | MapEmpty -> print_string "MapEmpty"
  in print m

let open_prec (p0:int) p = if p0 < p then print_char '('
let close_prec (p0:int) p = if p0 < p then print_char ')'

let print_bool b = print_string (if b then "true" else "false")

let rec print_aexp p = function
    ECon n -> print_z n
  | EVar v -> print_estr v
  | EPlus (l,r) -> open_prec 0 p; print_aexp 1 l ; print_string " + "; print_aexp 0 r; close_prec 0 p
  | EMinus (l,r) -> open_prec 0 p; print_aexp 1 l ; print_string " - "; print_aexp 0 r; close_prec 0 p
  | EDiv (l,r) -> open_prec 1 p; print_aexp 2 l ; print_string " / "; print_aexp 2 r; close_prec 1 p

let rec print_bexp p = function
    BCon b -> print_bool b
  | BLe (l,r) -> open_prec 1 p;print_aexp 0 l;print_string " <= ";print_aexp 0 r;close_prec 1 p
  | BNot b -> print_char '!';print_bexp 2 b
  | BAnd (l,r) -> open_prec 0 p;print_bexp 1 l;print_string " && ";print_bexp 0 r;close_prec 0 p

let rec print_stmt p = function
    Skip -> print_string "skip"
  | SAssign (v,e) -> print_estr v;print_string " := ";print_aexp 0 e;print_char ';'
  | Seq (s1,s2) -> open_prec 0 p;print_stmt 1 s1; print_char ' ';print_stmt 0 s2;close_prec 0 p
  | SIf (b,t,e) -> print_string "if (";print_bexp 0 b;print_string ") ";print_stmt 0 t;
                    print_string " else ";print_stmt p e
  | SWhile (c,b) -> print_string "while (";print_bexp 0 c;print_string ") ";print_stmt p b

let print_kitem = function
    KExp e -> print_aexp 0 e
  | KBExp b -> print_bexp 0 b
  | KStmt s -> print_stmt 0 s
  | KFreezeE _ | KFreezeB _ -> print_string "freezer"

let rec print_klist = function
    Nil -> print_string ".K"
  | Cons (k,Nil) -> print_kitem k
  | Cons (k,ks) -> print_kitem k; print_string " ~> "; print_klist ks


let print_cfg = function
  {kcell = k; store = s} -> print_string "<k>";print_klist k;print_string"</k>\n";
                            print_string "<store>";print_map print_z s;print_string "</store>";print_newline ()

let _ =
  let cfg0 = n_testcfg (read_int ())
  in print_cfg cfg0; print_string " =>";print_newline ();print_cfg (run cfg0);
