-- Prove2me | solution 1 for mme_dwz_positive_332_explicit_entropy_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:44:57.907984+00:00
-- url     : https://prove2.me/submissions/f928fee0-7546-4846-bb0c-482129f308ec

import Definitions.Def_mme_dwz_positive_332_entropy_certificate_data
import Theorems.Thm_mme_dwz_positive_332_branch_lower_bounds

open BigOperators MME MME.RecursiveYZ MME.DWZ332Fine MME.DWZ332Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem numerical_floor0 : (533226531 / 625000000 : ℚ) < coarseLower - penaltyUpper := by decide +kernel

private theorem numerical_floor1 : (533226531 / 625000000 : ℚ) < parentLower 1 - compatibilityUpper 0 := by decide +kernel

private theorem numerical_floor2 : (533226531 / 625000000 : ℚ) < parentLower 2 - compatibilityUpper 1 := by decide +kernel

theorem solution : (533226531 / 625000000 : ℝ) < explicitRate := by
  obtain ⟨hb0, hb1, hb2⟩ := mme_dwz_positive_332_branch_lower_bounds
  have h0 := numerical_floor0
  have h1 := numerical_floor1
  have h2 := numerical_floor2
  have hc0 : (533226531 / 625000000 : ℝ) < (coarseLower : ℝ) - penaltyUpper := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h0
    push_cast at h
    exact h
  have hc1 : (533226531 / 625000000 : ℝ) < (parentLower 1 : ℝ) - compatibilityUpper 0 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h1
    push_cast at h
    exact h
  have hc2 : (533226531 / 625000000 : ℝ) < (parentLower 2 : ℝ) - compatibilityUpper 1 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h2
    push_cast at h
    exact h
  unfold explicitRate
  exact lt_min (hc0.trans_le hb0) (lt_min (hc1.trans_le hb1) (hc2.trans_le hb2))
