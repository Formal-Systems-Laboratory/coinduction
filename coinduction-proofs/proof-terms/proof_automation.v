Require Import proof.

(** A generic proof strategy to go with proof.v *)
(**
   First, an general approach for the "upper levels"
   of the proof which seems to be quite effective in practice.

   Repeatedly do the first of the following which is possible
   1) Apply a specification rule by transitivity
   2) Take a step according to the semantics
   3) Make a case distinction, if we are blocked on a
   conditional with a symbolic value or suchlike.

   This works nicely if specifications are written so it's
   not possible to step too far, like if all code after the code
   we are constraining is represented by a variable (and we
   take care not to invent new statements to run in step 3).

   This tactic implements the above strategy with some refinements,
   taking tactics for each step.

   First, the tactic arguments can pause the overall execution
   process by failing at level 1 (perhaps by "fail 1" at the
   top level).
   This should be done when it seems the step should work, but
   couldn't be taken automatically, e.g. if a possible
   transitivity matches the current code but some side condition
   couldn't be solved automatically.
   Then the user can do something themselves before invoking the
   automation again.

   Second, the "hyp_check" tactic is called to help debugging
   new automation, it can be redefined to check any kind of
   well-definedness (e.g, if you want all abstract lists
   mentioned in goals to always be in some normal form,
   hyp_check could be redefined to check that no hypothesis
   contains a list in a bad form).

   The trans_tac should also try to put the goal back into the
   form this tactic can handle after successfully applying a
   transitivity (basically going from a new configuration variable
   restricted only by a predicate back to having a mostly-concrete
   configuration, and some useful hypotheses), but if it doesn't
   the tactic will just get stuck and wait for the user again.
   *)
Ltac hyp_check := idtac.
Ltac generic_step trans_tac step_solver split_stuck :=
    (hyp_check
    ||trans_tac
    ||(eapply dstep;[solve[step_solver]|])
    ||split_stuck
    ||fail (* this clause ensures we fail at level 0 when split_stuck fails at level 1 *)
    );instantiate;cbv beta.
Ltac generic_run trans_tac step_solver split_stuck done_solver :=
  repeat (generic_step trans_tac step_solver split_stuck)
  ;try solve[eapply ddone;done_solver].

(* For a simpler interface, we assume that chosing and applying
   a semantic or specification rule can be handled by
   econstructor (<side condition solver>) for respective
   correct choices of domain solvers.

   This further assumes that specifications are defined so
   any clause that even unifies is close enough to be worth
   pausing execution for

   More general tactics are still accepted for splitting stuck
   configurations, and also for getting from the general predicate
   postconditions of a transitivity back to a reachability goal.
   (though it does check generically if we are already at the
   final goal).
 *)
Ltac domain_trans_tac code_type trans_domain_solver trans_use_result :=
  eapply dtrans;[solve[econstructor(trans_domain_solver)]
              || econstructor;fail 1|];
  instantiate;simpl
 .
(*;try (
    solve[intro; eapply ddone

    ] || trans_use_result).
 *)

(*
Ltac domain_run trans_domain_solver trans_use_result step_domain_solver split_stuck done_tac
  := generic_run ltac:(domain_trans_tac trans_domain_solver trans_use_result)
                 ltac:(econstructor(step_domain_solver))
                 done_tac
                 split_stuck.
Ltac domain_step code_type trans_domain_solver trans_use_result step_domain_solver split_stuck
  := generic_step ltac:(domain_trans_tac code_type trans_domain_solver trans_use_result)
                  ltac:(econstructor(step_domain_solver))
                  split_stuck.
*)

Ltac domain_step trans_domain_solver trans_use_result step_domain_solver split_stuck :=
    (hyp_check
    ||(eapply dtrans;[solve[econstructor(trans_domain_solver)]
                     || econstructor;fail 1|];
       instantiate;simpl;try (
       solve[let k' := fresh "k'" in let Hk' := fresh "Hk'" in
             intros k' Hk'; eapply ddone; apply Hk'
       ] || trans_use_result))
    ||(eapply dstep;[solve[econstructor(step_domain_solver)]|])
    ||split_stuck
    ||fail (* this clause ensures we fail at level 0 when split_stuck fails at level 1 *)
    );instantiate;cbv beta.

Ltac domain_run trans_domain_solver trans_use_result step_domain_solver split_stuck done_tac :=
  repeat
    ((hyp_check
    ||(eapply dtrans;[solve[econstructor(trans_domain_solver)]
                     || econstructor;fail 1|];
       instantiate;simpl;try (
       solve[let k' := fresh "k'" in let Hk' := fresh "Hk'" in
             intros k' Hk'; eapply ddone; apply Hk'
       ] || trans_use_result))
    ||(eapply dstep;[solve[econstructor(step_domain_solver)]|])
    ||split_stuck
    ||fail (* this clause ensures we fail at level 0 when split_stuck fails at level 1 *)
    );instantiate;cbv beta);
   try solve[eapply ddone;done_tac].

