-- Prove2me | solution 1 for lean_workbook_plus_76560
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:29.654986+00:00
-- url     : https://prove2.me/submissions/04a686ea-d937-4017-a35d-9ebaf3bd1488

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ a b c : ℝ, a^5 + 3 * b^5 + c^5 ≥ 5 * a * b^3 * c) := by
  intro h
  have hh := h (-1) (-1) (-2)
  have hL : (-1 : ℝ)^5 + 3 * (-1)^5 + (-2)^5 = -36 := by ring
  have hR : (5 : ℝ) * (-1) * (-1)^3 * (-2) = -10 := by ring
  rw [hL, hR] at hh
  norm_num at hh

#print axioms solution
