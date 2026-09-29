-- Prove2me | solution 1 for lean_workbook_plus_15478
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:50:10.067768+00:00
-- url     : https://prove2.me/submissions/4b0cd638-349d-4ae8-992e-bbc1f7119a6e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, 1 > x ∧ x > 0 → ↑⌊x⌋ = 0 ∧ 0 ≤ √x ∧ √x < 1 := by
  intro x hx
  have hf : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hx.2.le,hx.1⟩
  constructor
  · simp [hf]
  · refine ⟨Real.sqrt_nonneg x, ?_⟩
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hx.2.le hx.1
