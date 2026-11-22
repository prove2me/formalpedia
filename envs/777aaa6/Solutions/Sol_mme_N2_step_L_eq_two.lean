-- Prove2me | solution 1 for mme_N2_step_L_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T17:26:00.8253+00:00
-- url     : https://prove2.me/submissions/4269263b-d95b-4893-9664-db7e4c64b952

import Theorems.Thm_mme_N2_lower_zero_or_one
import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : forall (lower : Nat)
    (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)),
    S.L = 2 := by
  intro lower S
  have h := mme_N2_lower_zero_or_one lower S
  have hlen := S.length
  rcases h with rfl | rfl
  · norm_num at hlen
    omega
  · norm_num at hlen
    omega
