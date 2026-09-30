-- Prove2me | solution 1 for lean_workbook_plus_78459
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:17.89087+00:00
-- url     : https://prove2.me/submissions/a9a1c081-e836-43e7-a56c-ee64e47dc814

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (x : ℝ) : x^4 > x - 1/2 := by
  by_contra h
  have hs : (x - 1/2)^2 = 0 := by
    nlinarith [sq_nonneg (x^2 - 1/2), sq_nonneg (x - 1/2)]
  have hx : x - 1/2 = 0 := sq_eq_zero_iff.mp hs
  have hx2 : x = 1/2 := sub_eq_zero.mp hx
  norm_num [hx2] at h
