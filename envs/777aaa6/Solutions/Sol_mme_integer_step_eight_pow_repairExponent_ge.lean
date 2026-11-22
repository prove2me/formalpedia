-- Prove2me | solution 1 for mme_integer_step_eight_pow_repairExponent_ge
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T15:52:23.307249+00:00
-- url     : https://prove2.me/submissions/b493a77b-51fe-4d2f-9e05-b072cae269f0

import Theorems.Thm_mme_integer_step_repairExponent_pos
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : forall {ell M : Nat} {P : MME.ProfiledCW.Predicate M}
    (S : MME.RegionRealization.IntegerStep ell M P),
    8 ≤ 8 ^ S.repairExponent := by
  intro ell M P S
  have h := mme_integer_step_repairExponent_pos S
  calc (8 : Nat) = 8 ^ 1 := by norm_num
  _ ≤ 8 ^ S.repairExponent := Nat.pow_le_pow_right (show 0 < 8 by norm_num) h
