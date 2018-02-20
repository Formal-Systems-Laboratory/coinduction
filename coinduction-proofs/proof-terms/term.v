(* Proof term. Unfortunately doesn't recheck as written *)
first_proof = 
proved_sound
  (fun (x : kcfg) (P : kcfg -> Prop) (H : loop_spec x P) =>
   match H in (loop_spec k P0) return (step kstep (trans kstep loop_spec) k P0) with
   | loop_claim x0 rest =>
      sstep (k_rule_33 eq_refl)
     (dstep (k_rule_0 eq_refl)
     (dstep (k_rule_18 eq_refl eq_refl)
     (dstep (k_rule_20 (same_item (Left Here) (equivRefl mapEmpty)))
     (dstep (k_rule_19 eq_refl eq_refl eq_refl)
     (dstep (k_rule_23 eq_refl)
     (dstep (k_rule_1 eq_refl eq_refl)
     (case_bool_spec (Z.leb_spec 0 x0)
     (fun _ : 0 <= x0 =>
        dstep (k_rule_31 eq_refl)
       (dstep k_rule_28
       (dstep (k_rule_30 eq_refl)
       (dstep k_rule_28
       (dstep (k_rule_2 eq_refl)
       (dstep (k_rule_6 eq_refl)
       (dstep (k_rule_20 (same_item (Left Here) (equivRefl mapEmpty)))
       (dstep (k_rule_7 eq_refl eq_refl)
       (dstep (k_rule_22 eq_refl)
       (dstep (k_rule_3 eq_refl eq_refl)
       (dstep (k_rule_29 eq_refl (same_item (Left Here) (equivRefl mapEmpty)))
       (dtrans (loop_claim (x0 + -1) rest)
             (fun (k' : kcfg) Hk' =>
          ddone Hk'))))))))))))) 
     (fun H0 : x0 < 0 =>
        dstep (k_rule_32 eq_refl)
       (dstep k_rule_27
       (ddone (conj eq_refl
              (ex_intro _ x0 (conj (equivUnit (kra "x" kdot |-> kra x0 kdot)) H0)))))))))))))
   end)
     : sound kstep loop_spec