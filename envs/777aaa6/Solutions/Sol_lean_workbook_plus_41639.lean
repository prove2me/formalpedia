-- Prove2me | solution 1 for lean_workbook_plus_41639
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:49.929178+00:00
-- url     : https://prove2.me/submissions/af9cbd3c-f093-40b3-a5d1-3030b28b55c2

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (h : a > 0) : (1 / Real.sqrt a) > 2 * (Real.sqrt (a + 1) - Real.sqrt a) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr h
  have hlt : Real.sqrt a < Real.sqrt (a + 1) := Real.sqrt_lt_sqrt h.le (by linarith)
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt h.le
  have h2 : Real.sqrt (a + 1) ^ 2 = a + 1 := Real.sq_sqrt (by linarith)
  have h3 : 0 < (Real.sqrt (a + 1) - Real.sqrt a) ^ 2 := by
    have := sub_pos.mpr hlt
    positivity
  rw [gt_iff_lt, lt_div_iff₀ hs]
  nlinarith
