-- Prove2me | solution 1 for lean_workbook_plus_39820
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:38.983643+00:00
-- url     : https://prove2.me/submissions/8ac03a37-9ae1-43cd-9fbc-8a32f89bd9df

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (h₁ : a = Real.sqrt (a * b)) (h₂ : b = (a + b) / 2) : a = b := by
  linarith
