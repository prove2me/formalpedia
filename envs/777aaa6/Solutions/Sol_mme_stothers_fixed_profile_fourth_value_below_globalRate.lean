-- Prove2me | solution 1 for mme_stothers_fixed_profile_fourth_value_below_globalRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:45:05.226203+00:00
-- url     : https://prove2.me/submissions/b4f5f686-cbe2-4ea4-9c4c-fbd73ae2858d

import Theorems.Thm_mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
import Theorems.Thm_mme_stothers_fixed_profile_outer_capacity
import Theorems.Thm_mme_stothers_fixed_exact_address_block_value
import Theorems.Thm_mme_stothers_fourth_support_and_classes

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

/-! The fixed numerical source theorem is exactly the structural assembly
specialized to `tau = 23737 / 30000`.  M1 supplies the literal support
condition, while the two remaining inputs are the scalar outer capacity and
the value of each exact-profile address block. -/

theorem solution
    {K : Type u} [Field K] :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 (23737 / 30000)
        MME.StothersFourth.fixedProfileB
        MME.StothersFourth.fixedProfileB →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6)
        (23737 / 30000) V := by
  apply mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
    (23737 / 30000)
  · intro sigma hnonzero
    have hsupp :=
      (mme_stothers_fourth_support_and_classes (K := K)).1 sigma
    by_contra hsum
    exact hnonzero (hsupp.mpr hsum)
  · exact mme_stothers_fixed_profile_outer_capacity (23737 / 30000)
  · exact mme_stothers_fixed_exact_address_block_value
      (23737 / 30000) (by norm_num) (by norm_num)

