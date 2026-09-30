-- Prove2me | solution 1 for lean_workbook_plus_81537
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:11.416674+00:00
-- url     : https://prove2.me/submissions/20e8d7c5-b2e3-4fb5-95df-168916245085

import Mathlib

theorem solution {a b c : ℝ} (h : a + b + c = 1) :
    a^3 + b^3 + c^3 - 3 * a * b * c ≥ 0 := by
  have hid : a^3 + b^3 + c^3 - 3 * a * b * c =
      a^2 + b^2 + c^2 - a*b - b*c - c*a := by
    calc
      _ = (a+b+c) * (a^2 + b^2 + c^2 - a*b - b*c - c*a) := by ring
      _ = _ := by rw [h, one_mul]
  rw [hid]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
