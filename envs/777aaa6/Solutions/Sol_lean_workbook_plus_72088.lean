-- Prove2me | solution 1 for lean_workbook_plus_72088
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-20T00:40:08.730968+00:00
-- url     : https://prove2.me/submissions/5fe40def-e493-48b6-8bc0-f4e7a28f1f18

import Mathlib.Analysis.Complex.Basic

theorem solution : (Real.sqrt 511 + Complex.I) * (Real.sqrt 511 - Complex.I) = 512 := by
  have h : ((Real.sqrt 511 : ℝ) : ℂ) ^ 2 = (511 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (511:ℝ) ≥ 0)]
    norm_num
  have key : (Real.sqrt 511 + Complex.I) * (Real.sqrt 511 - Complex.I)
           = ((Real.sqrt 511 : ℝ) : ℂ) ^ 2 - Complex.I ^ 2 := by ring
  rw [key, h, Complex.I_sq]; norm_num
