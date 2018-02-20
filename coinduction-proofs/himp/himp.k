module HIMP
syntax Int [hook(Int)]
syntax Map [hook(Map)]
syntax Bool ::=
    isValueMap(Map) [predicate, coq(is_value_map)]
syntax Struct [coq(sval)]
syntax Struct ::=
    Map [klabel(Struct),coq(Struct)]
syntax Undef ::= "undef" [coq(undef)]
syntax KResult ::=
    Int        [coq(Int)]
  | Bool       [coq(Bool)]
  | Struct     [coq(VStruct)]
  | Undef      [coq(VUndef)]
syntax Exps ::= List{Exp,","}
syntax Exp ::=
    Id              [coq(EVar)]
  | "load" Exp      [coq(strict,ELoad)]
  | Int             [coq(ECon)]
  | "-" Exp         [strict, coq(ENeg)]
  | Exp "+" Exp     [strict, coq(EPlus)]
  | Exp "-" Exp     [strict, coq(EMinus)]
  | Exp "*" Exp     [strict, coq(EMult)]
  | Exp "/" Exp     [strict, coq(EDiv)]
  | "build" Map     [coq(EBuild)]
  | Exp "." Id      [strict(1), coq(EProject)]
  | Id "(" Exps ")" [klabel(ecall),coq(ECall)]
  | "alloc"         [coq(EAlloc)]
  | Bool            [coq(BCon)]
  | Exp "<=" Exp    [strict,coq(BLe)]
  | Exp "<"  Exp    [strict,coq(BLt)]
  | Exp "==" Exp    [coq(BEq)]
  | "not" Exp      [strict,coq(BNot)]
  | Exp "and" Exp [strict(1), coq(BAnd)]
  | Exp "or"  Exp [strict(1), coq(BOr)]
  | Struct        [coq(EValStruct)]
syntax Stmt ::=
    "skip"           [coq(Skip)]
  | Id ":=" Exp      [strict(2), coq(SAssign)]
  | "*" Exp ":=" Exp [strict, coq(HAssign)]
  | "dealloc" Exp    [strict, coq(HDealloc)]
  | Stmt ";" Stmt    [coq(Seq)]
  | "if" Exp "then" "{" Stmt "}" "else" "{" Stmt "}"
                     [strict(1), coq(SIf)]
  | "while" Exp "do" "{" Stmt "}"
                     [coq(SWhile)]
  | "jump" Exp       [coq(Jump)]
  | "decl" Id        [coq(Decl)]
  | "return" Exp     [strict,coq(SReturn)]
  | "return"         [coq(SReturnVoid)]
  | Id "(" Exps ")"  [klabel(scall),coq(SCall)]
syntax Frame ::= frame(K,Map) [coq(frame)]

syntax Frames ::= List{Frame,","}
syntax Defn ::=
    Id "(" Ids ")" "{" Stmt "}" [coq(FunDef)]
syntax Ids ::= List{Id,","}
syntax Pgm ::= List{Defn,""} [klabel(_,Pgm_)]

configuration <k>($PGM:Pgm):>K</k>
             <env>.Map</env>
             <stk>.Frames</stk>
             <heap>.Map</heap>
             <funs>.Map</funs>
             <mark>0</mark>

// Evaluation rules
rule <k> F(Args){Body} P => P ...</k>
     <funs>... .Map => F |-> F(Args){Body} ...</funs> [label(k_next_defn)]
syntax Id ::= "main"
rule <k>.Pgm => (main(.Exps)::Stmt) </k> 
rule <k>I + J => I +Int J ...</k> [label(k_plus)]
rule <k>I * J => I *Int J ...</k> [label(k_mult)]
rule <k>I - J => I -Int J...</k> [label(k_minus)]
rule <k>- I => ~Int I...</k> [label(k_neg)]
rule <k>I / J => I /Int J ...</k>
     when 0 =/=Int J [label(k_div)]
rule <k>I <= J => I <=Int J ...</k> [label(k_le)]
rule <k>I < J => I <Int J ...</k> [label(k_lt)]
rule <k>I == J => I ==Int J ...</k> [label(k_eq)]
rule <k>not B => notBool B ...</k> [label(k_not)]
rule <k>true and B => B...</k> [label(k_and_t)]
rule <k>false and _ => false...</k> [label(k_and_f)]
rule <k>true or _ => true ...</k> [label(k_or_t)]
rule <k>false or B => B...</k> [label(k_or_f)]
rule <k>skip => .K...</k> [label(k_skip)]
rule <k>if true then {S} else {_} => S...</k> [label(k_if_t)]
rule <k>if false then {_} else {S} => S...</k> [label(k_if_f)]
rule <k>while B do {S}
     => if B then{S;while B do{S}} else {skip}...</k>
       [label(k_while)]
rule <k>'Struct (F::Id |-> V:KResult _) . F => V ...</k>
       [label(k_project)]
rule <k>I:Id => V:KResult...</k><env>...I |-> V...</env> [label(k_lookup)]
rule <k>build (V) => 'Struct(V)...</k> when isValueMap(V) [label(k_build)]

rule <k>alloc => M...</k>
     <heap>... .Map => M |-> undef ...</heap>
     <mark>M => M +Int 1</mark> [label(k_alloc)]
rule <k>dealloc(Addr:Int) => .K...</k><heap>... Addr |-> _ => .Map...</heap>
      [label(k_dealloc)]
rule <k>load(Addr:Int)=> V:KResult...</k><heap>...Addr|->V...</heap>
      [label(k_load)]
rule <k>X := V:KResult => .K...</k><env>... X |-> (_ => V) ...</env> [label(k_assign)]
rule <k>*Addr := V:KResult => .K...</k><heap>... Addr |-> (_ => V) ...</heap> [label(k_hassign)]
rule <k>decl X => .K...</k><env>... .Map => X |-> undef ...</env> [label(k_decl)]
/*
rule <k>`ecall`(F,Args) ~> Rest => Body</k>
     <funs>... `item`(F,`_(_){_}`(F,Formals,Body)) ...</funs>
     <env>Env => `mkMap`(Formals,Args)</env>
     <stk>Stk => `_,Frames_`(`frame`(Rest,Env),Stk)</stk>
  when `allValues`(Args) [label(k_call)]
rule <k>`scall`(F,Args) ~> Rest => Body</k>
     <funs>... `item`(F,`_(_){_}`(F,Formals,Body)) ...</funs>
     <env>Env => `mkMap`(Formals,Args)</env>
     <stk>Stk => `_,Frames_`(`frame`(Rest,Env),Stk)</stk>
  when `allValues`(Args) [label(k_scall)]
 */
rule <k>return (V:KResult) ~> _ => V ~> Rest</k>
     <env>_ => Env</env>
     <stk>frame(Rest,Env) , Stk => Stk</stk> [label(k_return)]
rule <k>return ~> _ => Rest</k>
     <env>_ => Env</env>
     <stk>frame(Rest,Env) , Stk => Stk</stk> [label(k_returnv)]

// Custom heating rules
rule <k>S1 ; S2 => S1 ~> S2 ...</k> [label(k_heat_seq)]

/*
// difficult heating rules
//   | k_heat_build : forall fields k, `(
//       find_unevaluated_entry fields = Some (v,k) ->
//       heat_step kstep (EBuild fields) v (KFreezeE (fun v' => EBuild (k v'))) rest)
//  | k_heat_call : forall f k, `(
//       first_unevaluated_arg nil args = Some (v, k) ->
//       heat_step kstep (Call f args) v (KFreezeE (fun v' => Call f (k v'))) rest)
//  | k_heat_scall : forall f k, `(
//       first_unevaluated_arg nil args = Some (v, k) ->
//       heat_step kstep (SCall f args) v (KFreezeE (fun v' => SCall f (k v'))) rest)
*/

endmodule
