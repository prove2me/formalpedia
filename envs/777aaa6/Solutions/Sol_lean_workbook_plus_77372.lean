-- Prove2me | solution 1 for lean_workbook_plus_77372
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:02.289616+00:00
-- url     : https://prove2.me/submissions/cf2a639c-f73d-4183-9e00-9abd6458bb3d

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (x y z a b c : ℝ)
    (ha : a^2 = Real.sqrt (x + y)) (hb : b^2 = Real.sqrt (y + z))
    (hc : c^2 = Real.sqrt (x + z)) :
    1 / a^2 + 1 / b^2 + 1 / c^2 ≥
      1 / (a * b) + 1 / (b * c) + 1 / (c * a) := by
  simp only [one_div, ← inv_pow, mul_inv_rev]
  nlinarith only [sq_nonneg (a⁻¹ - b⁻¹), sq_nonneg (b⁻¹ - c⁻¹),
    sq_nonneg (c⁻¹ - a⁻¹)]
