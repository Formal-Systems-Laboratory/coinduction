Require Import graph.

Definition schorr_waite_loop :=
  SWhile ("p" <> 0)
    {{ "t" <- "p"->>"left"
     ; "p" <<- build_tree ("p"->>"val" + 1)
                 ("p"->>"right") "q"
     ; SIf (("p"->>"val" = 3)
           || (("t" <> 0) && ("t"->>"val" = 0)))
         {{ "q" <- "p" ; "p" <- "t" }}
         {{ "q" <- "t" }}
    }}.
Definition schorr_waite_code :=
  SIf ("root" = 0) SReturnVoid
   {{ Decl "p"
    ; Decl "q"
    ; Decl "t"
    ; "p"<-"root"
    ; "q"<-0
    ; schorr_waite_loop
    ; SReturnVoid
    }}.
Definition schorr_waite_def :=
  FunDef "schorr_waite" ["root"] schorr_waite_code.
