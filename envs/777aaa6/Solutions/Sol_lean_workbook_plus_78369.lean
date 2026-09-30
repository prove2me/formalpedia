-- Prove2me | solution 1 for lean_workbook_plus_78369
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:58.930865+00:00
-- url     : https://prove2.me/submissions/a17f9ff8-bff3-4a5d-96dd-dcf0d8fbbfe6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0)
    (habc : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)
      ≥ 9 * a^2 * b^2 * c^2 := by
  nlinarith only [sq_nonneg (a * (b^2 - c^2)),
    sq_nonneg (b * (c^2 - a^2)), sq_nonneg (c * (a^2 - b^2))]
