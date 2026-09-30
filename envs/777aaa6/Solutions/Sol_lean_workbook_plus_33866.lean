-- Prove2me | solution 1 for lean_workbook_plus_33866
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:38.102017+00:00
-- url     : https://prove2.me/submissions/6cb73c77-b734-4337-bb5a-a8c2e68a3153

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h₁ : x + y = 10) (h₂ : x*y = 20) : x⁻¹ + y⁻¹ = 0.5 := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h₂
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h₂
  rw [inv_add_inv hx hy, h₂]
  rw [h₁]
  norm_num
