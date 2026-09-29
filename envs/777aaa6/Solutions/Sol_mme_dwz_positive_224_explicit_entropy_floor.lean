-- Prove2me | solution 1 for mme_dwz_positive_224_explicit_entropy_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:09:05.627188+00:00
-- url     : https://prove2.me/submissions/dd00ade1-ce13-4658-8a2f-fcdec2d79dbf

import Definitions.Def_mme_dwz_positive_224_entropy_certificate_data
import Theorems.Thm_mme_dwz_positive_224_branch_lower_bounds

open BigOperators MME MME.RecursiveYZ MME.DWZ224Fine MME.DWZ224Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem numerical_floor0 : (3910921057 / 5000000000 : ℚ) < coarseLower - penaltyUpper := by decide +kernel

private theorem numerical_floor1 : (3910921057 / 5000000000 : ℚ) < parentLower 1 - compatibilityUpper 0 := by decide +kernel

private theorem numerical_floor2 : (3910921057 / 5000000000 : ℚ) < parentLower 2 - compatibilityUpper 1 := by decide +kernel

theorem solution : (3910921057 / 5000000000 : ℝ) < explicitRate := by
  obtain ⟨hb0, hb1, hb2⟩ := mme_dwz_positive_224_branch_lower_bounds
  have h0 := numerical_floor0
  have h1 := numerical_floor1
  have h2 := numerical_floor2
  have hc0 : (3910921057 / 5000000000 : ℝ) < (coarseLower : ℝ) - penaltyUpper := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h0
    push_cast at h
    exact h
  have hc1 : (3910921057 / 5000000000 : ℝ) < (parentLower 1 : ℝ) - compatibilityUpper 0 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h1
    push_cast at h
    exact h
  have hc2 : (3910921057 / 5000000000 : ℝ) < (parentLower 2 : ℝ) - compatibilityUpper 1 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h2
    push_cast at h
    exact h
  unfold explicitRate
  exact lt_min (hc0.trans_le hb0) (lt_min (hc1.trans_le hb1) (hc2.trans_le hb2))
