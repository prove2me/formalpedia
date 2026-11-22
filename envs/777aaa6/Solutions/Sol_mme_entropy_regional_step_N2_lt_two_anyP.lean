-- Prove2me | solution 1 for mme_entropy_regional_step_N2_lt_two_anyP
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T14:57:55.00504+00:00
-- url     : https://prove2.me/submissions/71824dda-8270-40f7-9ead-359c7181d4d7

import Theorems.Thm_mme_integer_regional_step_N2_level_bound_anyP
import Theorems.Thm_mme_entropy_regional_step_L2_anyP_impossible
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data

set_option autoImplicit false

theorem solution : forall (lower : Nat) (P : MME.ProfiledCW.Predicate 2)
    (S : MME.RegionRealization.IntegerStep lower 2 P), lower < 2 := by
  intro lower P S
  have h3 := mme_integer_regional_step_N2_level_bound_anyP lower P S
  have hne : lower ≠ 2 := by
    intro h2
    subst h2
    exact mme_entropy_regional_step_L2_anyP_impossible P S
  omega
