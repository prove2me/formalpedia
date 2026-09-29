-- Prove2me | solution 1 for mme_dwz_positive_242_explicit_entropy_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:14:03.725014+00:00
-- url     : https://prove2.me/submissions/cbaba1b4-c37d-4b2b-bd9a-e12a2bb7c0bd

import Definitions.Def_mme_dwz_positive_242_entropy_certificate_data
import Theorems.Thm_mme_dwz_positive_242_branch_lower_bounds

open BigOperators MME MME.RecursiveYZ MME.DWZ242Fine MME.DWZ242Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem numerical_floor0 : (1992485517 / 2500000000 : ℚ) < coarseLower - penaltyUpper := by decide +kernel

private theorem numerical_floor1 : (1992485517 / 2500000000 : ℚ) < parentLower 1 - compatibilityUpper 0 := by decide +kernel

private theorem numerical_floor2 : (1992485517 / 2500000000 : ℚ) < parentLower 2 - compatibilityUpper 1 := by decide +kernel

theorem solution : (1992485517 / 2500000000 : ℝ) < explicitRate := by
  obtain ⟨hb0, hb1, hb2⟩ := mme_dwz_positive_242_branch_lower_bounds
  have h0 := numerical_floor0
  have h1 := numerical_floor1
  have h2 := numerical_floor2
  have hc0 : (1992485517 / 2500000000 : ℝ) < (coarseLower : ℝ) - penaltyUpper := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h0
    push_cast at h
    exact h
  have hc1 : (1992485517 / 2500000000 : ℝ) < (parentLower 1 : ℝ) - compatibilityUpper 0 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h1
    push_cast at h
    exact h
  have hc2 : (1992485517 / 2500000000 : ℝ) < (parentLower 2 : ℝ) - compatibilityUpper 1 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h2
    push_cast at h
    exact h
  unfold explicitRate
  exact lt_min (hc0.trans_le hb0) (lt_min (hc1.trans_le hb1) (hc2.trans_le hb2))
