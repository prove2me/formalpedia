-- Prove2me | solution 1 for lean_workbook_plus_28691
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:43:42.641964+00:00
-- url     : https://prove2.me/submissions/2900a5e5-9278-4266-9471-2cc4a0244dcf

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ)
  (h₀ : a + b + c = 7 - d)
  (h₁ : a^2 + b^2 + c^2 = 13 - d^2) :
  3 * (a^2 + b^2 + c^2) ≥ (a + b + c)^2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
