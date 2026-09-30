-- Prove2me | solution 1 for lean_workbook_plus_79170
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:18.093653+00:00
-- url     : https://prove2.me/submissions/2ec4740d-dbff-4f5b-b381-4ebf2e611c76

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + Real.sqrt (a * b)) / 2 ≤ Real.sqrt (a * (a + b) / 2) := by
  apply Real.le_sqrt_of_sq_le
  have hs := Real.sq_sqrt (mul_nonneg ha hb)
  nlinarith only [hs, sq_nonneg (a - Real.sqrt (a * b))]
