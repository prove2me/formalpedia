-- Prove2me | solution 1 for mme_entropy_regional_step_N2_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T14:39:00.326863+00:00
-- url     : https://prove2.me/submissions/994db34b-b4b9-4caf-8b9f-3f4f460cbf6c

import Theorems.Thm_mme_integer_regional_step_N2_level_bound
import Theorems.Thm_mme_entropy_regional_step_L2_N2_impossible
import Definitions.Def_mme_integer_regional_CW_recipe

set_option autoImplicit false

theorem solution : forall (lower : Nat) (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)), lower < 2 := by
  intro lower S
  have h3 := mme_integer_regional_step_N2_level_bound lower S
  have hne : lower ≠ 2 := by
    intro h2
    subst h2
    exact mme_entropy_regional_step_L2_N2_impossible S
  omega
