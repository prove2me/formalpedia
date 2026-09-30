-- Prove2me | solution 1 for lean_workbook_plus_38763
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:28.274477+00:00
-- url     : https://prove2.me/submissions/8735c284-9d6f-4e60-8769-425b584dd4a9

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (h : a > 0) : 1 / Real.sqrt a > 2 * (Real.sqrt (a + 1) - Real.sqrt a) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr h
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt h.le
  have ht2 : Real.sqrt (a + 1) ^ 2 = a + 1 := Real.sq_sqrt (by linarith)
  have hlt : Real.sqrt a < Real.sqrt (a + 1) := Real.sqrt_lt_sqrt h.le (by linarith)
  have hpos : 0 < (Real.sqrt (a + 1) - Real.sqrt a) ^ 2 := by
    have := sub_pos.mpr hlt
    positivity
  rw [gt_iff_lt, lt_div_iff₀ hs]
  nlinarith [hpos, hs2, ht2]
