-- Prove2me | solution 1 for tan_add_eq_spb
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:16:58.954562+00:00
-- url     : https://prove2.me/submissions/8fb37aa7-c4c5-4933-8dd2-bf258acc3896

-- Sol generated from Shared/AbstractAlgebra/Spb_hasDerivAt_snd.lean
import Mathlib
import Definitions.Def_Shared_AbstractAlgebra_Spb_hasDerivAt_snd

/-! # CatalogBuild.Shared.Spb_hasDerivAt_snd

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 8
-/

noncomputable section














theorem solution(x y : ℝ) (hx : Real.cos x ≠ 0) (hy : Real.cos y ≠ 0) :
    Real.tan (x + y) = spb (Real.tan x) (Real.tan y) := by
  have hd : 1 - Real.tan x * Real.tan y
      = (Real.cos x * Real.cos y - Real.sin x * Real.sin y) / (Real.cos x * Real.cos y) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    field_simp
  by_cases h : Real.cos (x + y) = 0
  · have h0 : Real.cos x * Real.cos y - Real.sin x * Real.sin y = 0 := by
      rw [← Real.cos_add]; exact h
    unfold spb
    rw [hd, h0, zero_div, div_zero, Real.tan_eq_sin_div_cos, h, div_zero]
  · unfold spb
    rw [Real.tan_eq_sin_div_cos (x + y), Real.sin_add, Real.cos_add,
        Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    rw [Real.cos_add] at h
    field_simp
