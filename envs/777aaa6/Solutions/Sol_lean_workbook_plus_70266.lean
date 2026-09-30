-- Prove2me | solution 1 for lean_workbook_plus_70266
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:29:26.559388+00:00
-- url     : https://prove2.me/submissions/4885d97f-fe59-43ce-8a02-628c34f5158f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (b : ℝ) : 90 ≥ b ^ 2 + 4 ^ 2 + 6 ^ 2 → b ≤ Real.sqrt 38 := by
  intro h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 38 by norm_num)
  have hn := Real.sqrt_nonneg (38 : ℝ)
  by_contra hb
  have hh : Real.sqrt 38 < b := lt_of_not_ge hb
  nlinarith

#print axioms solution
