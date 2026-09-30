-- Prove2me | solution 1 for lean_workbook_plus_55287
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:57.430717+00:00
-- url     : https://prove2.me/submissions/7ed2e8db-5e6f-4b62-a2b1-8437c171982b

import Mathlib.Analysis.Complex.Basic

theorem solution : √(8 + 4 * Real.sqrt 3) = √6 + √2 := by
  have h6 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h2 : (√2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (√3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h : (√6 + √2)^2 = 8 + 4 * Real.sqrt 3 := by
    rw [h6]
    linear_combination ((√3)^2 + 2 * √3 + 1) * h2 + 2 * h3
  rw [← h, Real.sqrt_sq (by positivity)]
