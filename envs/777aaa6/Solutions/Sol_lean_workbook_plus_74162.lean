-- Prove2me | solution 1 for lean_workbook_plus_74162
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:06.344378+00:00
-- url     : https://prove2.me/submissions/7db644c4-8309-4f88-b81a-1b86b7ce2ee7

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b + b * c + c * a = 1) :
    Real.sqrt (1 + a ^ 2) ≤ (a + b + (a + c)) / 2 := by
  apply (Real.sqrt_le_left (by linarith : 0 ≤ (a + b + (a + c)) / 2)).2
  nlinarith only [habc, sq_nonneg (b - c)]
