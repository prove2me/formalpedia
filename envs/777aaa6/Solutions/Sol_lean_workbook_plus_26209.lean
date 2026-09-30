-- Prove2me | solution 1 for lean_workbook_plus_26209
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:03:26.171489+00:00
-- url     : https://prove2.me/submissions/6fb3c2f8-c5fa-453f-86d8-28ba58e8ab31

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) :
    Real.sqrt (2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) ≥
    (a + b) * (b + c) * (c + a) - 4 * a * b * c := by
  apply Real.le_sqrt_of_sq_le
  have hid :
      2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) -
        ((a + b) * (b + c) * (c + a) - 4 * a * b * c) ^ 2 =
      ((a - b) * (b - c) * (c - a)) ^ 2 := by ring
  nlinarith only [hid, sq_nonneg ((a - b) * (b - c) * (c - a))]
