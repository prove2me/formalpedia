-- Prove2me | solution 1 for lean_workbook_plus_18955
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:05.690576+00:00
-- url     : https://prove2.me/submissions/8b3535bc-7a04-4a6f-8482-4693dbf043f0

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : abs a < 1) (hb : abs b < 1) : abs (a + b) / (1 + a * b) < 1 := by
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  have hpos : 0 < 1 + a * b := by nlinarith
  rw [div_lt_one hpos, abs_lt]
  constructor <;> nlinarith
