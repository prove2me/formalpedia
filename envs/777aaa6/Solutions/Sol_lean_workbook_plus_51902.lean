-- Prove2me | solution 1 for lean_workbook_plus_51902
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:23.98042+00:00
-- url     : https://prove2.me/submissions/b9d4cc54-a0cd-4064-a5eb-5d5d6154da30

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (f_def : f = fun x => -(4/3)*x^2 -(14/3)*x + (8/3)) : f (-1) = 6 := by
  subst f_def
  norm_num
