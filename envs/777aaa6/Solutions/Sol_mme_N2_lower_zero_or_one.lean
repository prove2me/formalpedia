-- Prove2me | solution 1 for mme_N2_lower_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T17:24:42.858527+00:00
-- url     : https://prove2.me/submissions/9283605c-1122-4c37-bcf5-39c948361a94

import Theorems.Thm_mme_entropy_regional_step_N2_lt_two
import Definitions.Def_mme_integer_regional_CW_recipe

set_option autoImplicit false

theorem solution : forall (lower : Nat)
    (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)),
    lower = 0 ∨ lower = 1 := by
  intro lower S
  have h := mme_entropy_regional_step_N2_lt_two lower S
  omega
