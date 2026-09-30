-- Prove2me | solution 1 for lean_workbook_plus_42648
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:56:36.925236+00:00
-- url     : https://prove2.me/submissions/3df893d7-8b5b-48e1-b14c-905c15174a9c

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (h₀ : x = (1 + Real.sqrt 5) / 2) : x^2 - x - 1 = 0 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  subst h₀
  nlinarith [h5]
