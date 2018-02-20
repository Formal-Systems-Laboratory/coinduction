Require Export himp_syntax.
Require Export himp_cfg_and_prims.

Set Implicit Arguments.

Inductive kstep : kcfg -> kcfg -> Prop :=
 | k_cool_i : forall i e rest,
     kcell_step kstep (kra (KInt i) (kra (KFreeze e) rest))
                      (kra (cool_exp_kitem (ECon i) e) rest)
 | k_cool_b : forall b e rest,
     kcell_step kstep (kra (KBool b) (kra (KFreeze e) rest))
                      (kra (cool_exp_kitem (BCon b) e) rest)
 | k_cool_s : forall s e rest,
     kcell_step kstep (kra (KStruct s) (kra (KFreeze e) rest))
                      (kra (cool_exp_kitem (EValStruct s) e) rest)
 | k_heat_build : forall fields v k rest,
       find_unevaluated_entry fields = Some (v,k) ->
       heat_step kstep (KExp (EBuild fields)) v (KFreeze (KExp (EBuild k))) rest
 | k_heat_call : forall args v k f rest,
       first_unevaluated_arg nil args = Some (v, k) ->
       heat_step kstep (KExp (ECall f args)) v (KFreeze (KExp (ECall f k))) rest
 | k_heat_scall : forall args v k f rest,
       first_unevaluated_arg nil args = Some (v, k) ->
       heat_step kstep (KStmt (SCall f args)) v (KFreeze (KStmt (SCall f k))) rest
 | k_build : forall fields rest,
       is_value_map fields = true ->
       krule kstep [k_cell (write (kra (KExp (EBuild fields)) rest) (kra (KStruct (Struct fields)) rest))]
 | k_next_defn : forall Args Body F P WildVar1 WildVar2, krule kstep [k_cell (write (kra (KPgm (cons (FunDef F Args Body) P)) WildVar1) (kra (KPgm P) WildVar1)); fun_cell (write WildVar2 (kra (KId F) kdot |-> kra (KDefn (FunDef F Args Body)) kdot :* WildVar2))]
 | k_plus : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (EPlus (ECon I) (ECon J))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KInt (Zplus I J)) WildVar1))]
 | k_mult : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (EMult (ECon I) (ECon J))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KInt (Zmult I J)) WildVar1))]
 | k_minus : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (EMinus (ECon I) (ECon J))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KInt (Zminus I J)) WildVar1))]
 | k_neg : forall I WildVar1 x1, eq (ExpFromK x1) (Some (ENeg (ECon I))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KInt (Zopp I)) WildVar1))]
 | k_div : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (EDiv (ECon I) (ECon J))) -> eq (Zneq_bool 0 J) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KInt (Zdiv I J)) WildVar1))]
 | k_le : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (BLe (ECon I) (ECon J))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KBool (Zle_bool I J)) WildVar1))]
 | k_lt : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (BLt (ECon I) (ECon J))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KBool (Zlt_bool I J)) WildVar1))]
 | k_eq : forall I J WildVar1 x1, eq (ExpFromK x1) (Some (BEq (ECon I) (ECon J))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KBool (Z.eqb I J)) WildVar1))]
 | k_not : forall B WildVar1 x1, eq (ExpFromK x1) (Some (BNot (BCon B))) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KBool (negb B)) WildVar1))]
 | k_and_t : forall B WildVar1 x1, eq (ExpFromK x1) (Some (BAnd (BCon true) B)) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK B) WildVar1))]
 | k_and_f : forall WildVar1 WildVar2 x1, eq (ExpFromK x1) (Some (BAnd (BCon false) WildVar1)) -> krule kstep [k_cell (write (kra x1 WildVar2) (kra (KBool false) WildVar2))]
 | k_or_t : forall WildVar1 WildVar2 x1, eq (ExpFromK x1) (Some (BOr (BCon true) WildVar1)) -> krule kstep [k_cell (write (kra x1 WildVar2) (kra (KBool true) WildVar2))]
 | k_or_f : forall B WildVar1 x1, eq (ExpFromK x1) (Some (BOr (BCon false) B)) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK B) WildVar1))]
 | k_skip : forall WildVar1, krule kstep [k_cell (write (kra (KStmt Skip) WildVar1) WildVar1)]
 | k_if_t : forall S WildVar1 WildVar2, krule kstep [k_cell (write (kra (KStmt (SIf (BCon true) S WildVar1)) WildVar2) (kra (KStmt S) WildVar2))]
 | k_if_f : forall S WildVar1 WildVar2, krule kstep [k_cell (write (kra (KStmt (SIf (BCon false) WildVar1 S)) WildVar2) (kra (KStmt S) WildVar2))]
 | k_while : forall B S WildVar1, krule kstep [k_cell (write (kra (KStmt (SWhile B S)) WildVar1) (kra (KStmt (SIf B (Seq S (SWhile B S)) Skip)) WildVar1))]
 | k_project : forall F V WildVar1 WildVar2 x1 x2 x3, eq (ExpFromK x1) (Some (EProject (EValStruct (Struct x2)) F)) -> MapEquiv x2 (kra (KId F) kdot |-> kra x3 kdot :* WildVar1) -> eq (KResultFromK x3) (Some V) -> krule kstep [k_cell (write (kra x1 WildVar2) (kra (KResultToK V) WildVar2))]
 | k_lookup : forall I V WildVar1 WildVar2 x1 x2, MapEquiv x1 (kra (KId I) kdot |-> kra x2 kdot :* WildVar1) -> eq (KResultFromK x2) (Some V) -> krule kstep [k_cell (write (kra (KId I) WildVar2) (kra (KResultToK V) WildVar2)); env_cell (write x1 (kra (KId I) kdot |-> kra (KResultToK V) kdot :* WildVar1))]
 | k_alloc : forall M WildVar1 WildVar2 x1, eq (ExpFromK x1) (Some EAlloc) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KInt M) WildVar1)); heap_cell (write WildVar2 (kra (KInt M) kdot |-> kra (KUndef undef) kdot :* WildVar2)); mark_cell (write M (Zplus M 1))]
 | k_dealloc : forall Addr WildVar1 WildVar2 WildVar3 x1, MapEquiv x1 (kra (KInt Addr) kdot |-> WildVar1 :* WildVar3) -> krule kstep [k_cell (write (kra (KStmt (HDealloc (ECon Addr))) WildVar2) WildVar2); heap_cell (write x1 WildVar3)]
 | k_load : forall Addr V WildVar1 WildVar2 x1 x2 x3, eq (ExpFromK x1) (Some (ELoad (ECon Addr))) -> MapEquiv x2 (kra (KInt Addr) kdot |-> kra x3 kdot :* WildVar2) -> eq (KResultFromK x3) (Some V) -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (KResultToK V) WildVar1)); heap_cell (write x2 (kra (KInt Addr) kdot |-> kra (KResultToK V) kdot :* WildVar2))]
 | k_assign : forall V WildVar1 WildVar2 WildVar3 X x1 x2, eq (KResultFromExp x1) (Some V) -> MapEquiv x2 (kra (KId X) kdot |-> WildVar1 :* WildVar3) -> krule kstep [k_cell (write (kra (KStmt (SAssign X x1)) WildVar2) WildVar2); env_cell (write x2 (kra (KId X) kdot |-> kra (KResultToK V) kdot :* WildVar3))]
 | k_hassign : forall Addr V WildVar1 WildVar2 WildVar3 x1 x2, eq (KResultFromExp x1) (Some V) -> MapEquiv x2 (kra (KInt Addr) kdot |-> WildVar1 :* WildVar3) -> krule kstep [k_cell (write (kra (KStmt (HAssign (ECon Addr) x1)) WildVar2) WildVar2); heap_cell (write x2 (kra (KInt Addr) kdot |-> kra (KResultToK V) kdot :* WildVar3))]
 | k_decl : forall WildVar1 WildVar2 X, krule kstep [k_cell (write (kra (KStmt (Decl X)) WildVar1) WildVar1); env_cell (write WildVar2 (kra (KId X) kdot |-> kra (KUndef undef) kdot :* WildVar2))]
 | k_call : forall Args Body Env F Formals Rest Stk WildVar1 x1 x2, eq (ExpFromK x1) (Some (ECall F Args)) -> MapEquiv x2 (kra (KId F) kdot |-> kra (KDefn (FunDef F Formals Body)) kdot :* WildVar1) -> eq (all_values Args) true -> krule kstep [k_cell (write (kra x1 Rest) (kra (KStmt Body) kdot)); fun_cell (write x2 (kra (KId F) kdot |-> kra (KDefn (FunDef F Formals Body)) kdot :* WildVar1)); env_cell (write Env (mkMap Formals Args)); stk_cell (write Stk (cons (frame Rest Env) Stk))]
 | k_scall : forall Args Body Env F Formals Rest Stk WildVar1 x1, MapEquiv x1 (kra (KId F) kdot |-> kra (KDefn (FunDef F Formals Body)) kdot :* WildVar1) -> eq (all_values Args) true -> krule kstep [k_cell (write (kra (KStmt (SCall F Args)) Rest) (kra (KStmt Body) kdot)); fun_cell (write x1 (kra (KId F) kdot |-> kra (KDefn (FunDef F Formals Body)) kdot :* WildVar1)); env_cell (write Env (mkMap Formals Args)); stk_cell (write Stk (cons (frame Rest Env) Stk))]
 | k_return : forall Env Rest Stk V WildVar1 WildVar2 x1, eq (KResultFromExp x1) (Some V) -> krule kstep [k_cell (write (kra (KStmt (SReturn x1)) WildVar1) (kra (KResultToK V) Rest)); env_cell (write WildVar2 Env); stk_cell (write (cons (frame Rest Env) Stk) Stk)]
 | k_returnv : forall Env Rest Stk WildVar1 WildVar2, krule kstep [k_cell (write (kra (KStmt SReturnVoid) WildVar1) Rest); env_cell (write WildVar2 Env); stk_cell (write (cons (frame Rest Env) Stk) Stk)]
 | k_heat_load : forall E WildVar1 x1, eq (ExpFromK x1) (Some (ELoad E)) -> eq (notKResult (kra (ExpToK E) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK E) (kra (KFreeze (ExpToK (ELoad HOLE_Exp))) WildVar1)))]
 | k_heat_plus_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EPlus X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (EPlus HOLE_Exp Y))) WildVar1)))]
 | k_heat_plus_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EPlus X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (EPlus X HOLE_Exp))) WildVar1)))]
 | k_heat_minus_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EMinus X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (EMinus HOLE_Exp Y))) WildVar1)))]
 | k_heat_minus_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EMinus X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (EMinus X HOLE_Exp))) WildVar1)))]
 | k_heat_neg : forall WildVar1 X x1, eq (ExpFromK x1) (Some (ENeg X)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (ENeg HOLE_Exp))) WildVar1)))]
 | k_heat_mult_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EMult X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (EMult HOLE_Exp Y))) WildVar1)))]
 | k_heat_mult_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EMult X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (EMult X HOLE_Exp))) WildVar1)))]
 | k_heat_div_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EDiv X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (EDiv HOLE_Exp Y))) WildVar1)))]
 | k_heat_div_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (EDiv X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (EDiv X HOLE_Exp))) WildVar1)))]
 | k_heat_le_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (BLe X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (BLe HOLE_Exp Y))) WildVar1)))]
 | k_heat_le_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (BLe X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (BLe X HOLE_Exp))) WildVar1)))]
 | k_heat_lt_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (BLt X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (BLt HOLE_Exp Y))) WildVar1)))]
 | k_heat_lt_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (BLt X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (BLt X HOLE_Exp))) WildVar1)))]
 | k_heat_eq_l : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (BEq X Y)) -> eq (notKResult (kra (ExpToK X) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK X) (kra (KFreeze (ExpToK (BEq HOLE_Exp Y))) WildVar1)))]
 | k_heat_eq_r : forall WildVar1 X Y x1, eq (ExpFromK x1) (Some (BEq X Y)) -> eq (notKResult (kra (ExpToK Y) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK Y) (kra (KFreeze (ExpToK (BEq X HOLE_Exp))) WildVar1)))]
 | k_heat_not : forall B WildVar1 x1, eq (ExpFromK x1) (Some (BNot B)) -> eq (notKResult (kra (ExpToK B) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK B) (kra (KFreeze (ExpToK (BNot HOLE_Exp))) WildVar1)))]
 | k_heat_and : forall B C WildVar1 x1, eq (ExpFromK x1) (Some (BAnd B C)) -> eq (notKResult (kra (ExpToK B) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK B) (kra (KFreeze (ExpToK (BAnd HOLE_Exp C))) WildVar1)))]
 | k_heat_or : forall B C WildVar1 x1, eq (ExpFromK x1) (Some (BOr B C)) -> eq (notKResult (kra (ExpToK B) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK B) (kra (KFreeze (ExpToK (BOr HOLE_Exp C))) WildVar1)))]
 | k_heat_assign : forall E V WildVar1, eq (notKResult (kra (ExpToK E) kdot)) true -> krule kstep [k_cell (write (kra (KStmt (SAssign V E)) WildVar1) (kra (ExpToK E) (kra (KFreeze (KStmt (SAssign V HOLE_Exp))) WildVar1)))]
 | k_heat_hassign_l : forall E1 E2 WildVar1, eq (notKResult (kra (ExpToK E1) kdot)) true -> krule kstep [k_cell (write (kra (KStmt (HAssign E1 E2)) WildVar1) (kra (ExpToK E1) (kra (KFreeze (KStmt (HAssign HOLE_Exp E2))) WildVar1)))]
 | k_heat_hassign_r : forall E1 E2 WildVar1, eq (notKResult (kra (ExpToK E2) kdot)) true -> krule kstep [k_cell (write (kra (KStmt (HAssign E1 E2)) WildVar1) (kra (ExpToK E2) (kra (KFreeze (KStmt (HAssign E1 HOLE_Exp))) WildVar1)))]
 | k_heat_dealloc : forall E WildVar1, eq (notKResult (kra (ExpToK E) kdot)) true -> krule kstep [k_cell (write (kra (KStmt (HDealloc E)) WildVar1) (kra (ExpToK E) (kra (KFreeze (KStmt (HDealloc HOLE_Exp))) WildVar1)))]
 | k_heat_project_l : forall E F WildVar1 x1, eq (ExpFromK x1) (Some (EProject E F)) -> eq (notKResult (kra (ExpToK E) kdot)) true -> krule kstep [k_cell (write (kra x1 WildVar1) (kra (ExpToK E) (kra (KFreeze (ExpToK (EProject HOLE_Exp F))) WildVar1)))]
 | k_heat_if : forall B S1 S2 WildVar1, eq (notKResult (kra (ExpToK B) kdot)) true -> krule kstep [k_cell (write (kra (KStmt (SIf B S1 S2)) WildVar1) (kra (ExpToK B) (kra (KFreeze (KStmt (SIf HOLE_Exp S1 S2))) WildVar1)))]
 | k_heat_return : forall E WildVar1, eq (notKResult (kra (ExpToK E) kdot)) true -> krule kstep [k_cell (write (kra (KStmt (SReturn E)) WildVar1) (kra (ExpToK E) (kra (KFreeze (KStmt (SReturn HOLE_Exp))) WildVar1)))]
 | k_heat_seq : forall S1 S2 WildVar1, krule kstep [k_cell (write (kra (KStmt (Seq S1 S2)) WildVar1) (kra (KStmt S1) (kra (KStmt S2) WildVar1)))]
.
