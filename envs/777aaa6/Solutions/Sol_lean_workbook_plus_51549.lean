-- Prove2me | solution 1 for lean_workbook_plus_51549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:24:56.71255+00:00
-- url     : https://prove2.me/submissions/71e509e4-b948-4541-a219-64dd3ad657dc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (m n : ℝ) (h₁ : m ≥ 0 ∧ n ≥ 0) (h₂ : m ≠ 0) : 2 * Real.sqrt m * (Real.sqrt m + Real.sqrt n) * (Real.sqrt m + Real.sqrt n) / (2 * Real.sqrt m) = (Real.sqrt m + Real.sqrt n) ^ 2 := by
  have hm : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne h₁.1 (Ne.symm h₂)))
  field_simp
  <;> ring
